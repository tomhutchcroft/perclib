/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original two-sided summation proofs for the deleted lace diagrams;
no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.Chains
public import PercLib.Percolation.Bond.Lace.Diagrams.Bounds
public import PercLib.Percolation.Bond.Lace.Diagrams.ReverseBounds

/-!
# Summing a marked connector from both ends

## Main results

The backward iterate has its own mass bound and transport API. Cutting the
actual diagram at a connector separates a forward prefix from a backward
suffix. A common translation then isolates the marked connector core,
keeping the two geometric constants separate and preserving bond deletion.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- The backward mass is controlled by the actual `B C_d` column bound. -/
theorem diagramReverseIterate_mass_le_geometric (q : Sym2 V → unitInterval)
    (y : V) (σ : ℝ≥0∞)
    (hσ : ∀ p, (∑' s, ∑' r, diagramInterior q s r * diagramConnector q r p) ≤ σ)
    (n : ℕ) :
    (∑' p, diagramReverseIterate q y n p) ≤
      (∑' u, ∑' v, tau q y u * tau q u v * tau q v y) * σ ^ n := by
  classical
  induction n with
  | zero =>
    simp only [diagramReverseIterate_zero, pow_zero, mul_one]
    rw [ENNReal.tsum_prod']
    apply le_of_eq
    apply tsum_congr
    intro u
    apply tsum_congr
    intro v
    rw [tau_comm q u y]
    ac_rfl
  | succ n ih =>
    calc
      _ = ∑' t, (∑' s, ∑' r, diagramInterior q s r * diagramConnector q r t) *
          diagramReverseIterate q y n t := by
        simp only [diagramReverseIterate_succ]
        symm
        simp_rw [← ENNReal.tsum_mul_right]
        simpa only [ENNReal.tsum_prod'] using
          (ENNReal.tsum_comm (f := fun t (p : (V × V) × (V × V)) =>
            diagramInterior q p.1 p.2 * diagramConnector q p.2 t *
              diagramReverseIterate q y n t))
      _ ≤ ∑' t, σ * diagramReverseIterate q y n t :=
        ENNReal.tsum_le_tsum fun t => mul_le_mul' (hσ t) le_rfl
      _ = σ * ∑' t, diagramReverseIterate q y n t := ENNReal.tsum_mul_left
      _ ≤ σ * ((∑' u, ∑' v, tau q y u * tau q u v * tau q v y) * σ ^ n) :=
        mul_le_mul' le_rfl ih
      _ = _ := by rw [pow_succ]; ac_rfl

/-- The same law transport used for connections respects deletion of the
corresponding bond. -/
theorem law_deleted_conn_apply_equiv (q : Sym2 V → unitInterval) (e : V ≃ V)
    (hq : ∀ a, q (Sym2.map e a) = q a) (u v a b : V) :
    law q {ω : Config V | ω \ {s(e u, e v)} ∈ conn (e a) (e b)} =
      law q {ω : Config V | ω \ {s(u, v)} ∈ conn a b} := by
  classical
  have hmap : (law q).map (fun ω => Sym2.map e '' ω) = law q :=
    PercLib.Probability.prodBernoulli_map_image_sym2_invariant q e hq
  calc
    _ = ((law q).map (fun ω => Sym2.map e '' ω))
        {ω : Config V | ω \ {s(e u, e v)} ∈ conn (e a) (e b)} := by rw [hmap]
    _ = law q ((fun ω : Config V => Sym2.map e '' ω) ⁻¹'
        {ω : Config V | ω \ {s(e u, e v)} ∈ conn (e a) (e b)}) :=
      map_image_sym2Map_apply e (law q) _
    _ = _ := by
      congr 1
      ext ω
      change (Sym2.map e '' ω) \ {s(e u, e v)} ∈ conn (e a) (e b) ↔ _
      rw [← image_sym2Map_sdiff_singleton, image_mem_conn_iff]
      rfl

/-- The deleted connector is covariant under a profile-preserving bijection. -/
theorem diagramConnector_apply_equiv (q : Sym2 V → unitInterval) (e : V ≃ V)
    (hq : ∀ a, q (Sym2.map e a) = q a) (p r : V × V) :
    diagramConnector q (e p.1, e p.2) (e r.1, e r.2) = diagramConnector q p r := by
  classical
  unfold diagramConnector
  rw [← e.tsum_eq]
  apply tsum_congr
  intro v
  rw [offDiagonal_apply_equiv q e hq, law_deleted_conn_apply_equiv q e hq,
    tau_eq_of_map_law e (PercLib.Probability.prodBernoulli_map_image_sym2_invariant q e hq)]

/-- Both interior geometries, including their excluded diagonal, are covariant. -/
theorem diagramInterior_apply_equiv (q : Sym2 V → unitInterval) (e : V ≃ V)
    (hq : ∀ a, q (Sym2.map e a) = q a) (p r : V × V) :
    diagramInterior q (e p.1, e p.2) (e r.1, e r.2) = diagramInterior q p r := by
  classical
  have hτ := tau_eq_of_map_law e
    (PercLib.Probability.prodBernoulli_map_image_sym2_invariant q e hq)
  simp only [diagramInterior, hτ, e.injective.eq_iff]
  congr 1
  split_ifs with h
  · congr 1
    rw [← e.tsum_eq]
    apply tsum_congr
    intro z
    simp only [e.injective.eq_iff, hτ]
  · rfl

/-- Transport of the backward iterate follows the original order of its factors. -/
theorem diagramReverseIterate_apply_equiv (q : Sym2 V → unitInterval) (e : V ≃ V)
    (hq : ∀ a, q (Sym2.map e a) = q a) (y : V) (n : ℕ) (p : V × V) :
    diagramReverseIterate q (e y) n (e p.1, e p.2) = diagramReverseIterate q y n p := by
  classical
  induction n generalizing p with
  | zero =>
    simp only [diagramReverseIterate_zero,
      tau_eq_of_map_law e (PercLib.Probability.prodBernoulli_map_image_sym2_invariant q e hq)]
  | succ n ih =>
    rw [diagramReverseIterate_succ, diagramReverseIterate_succ,
      ← (Equiv.prodCongr e e).tsum_eq]
    apply tsum_congr
    intro r
    rw [← (Equiv.prodCongr e e).tsum_eq]
    apply tsum_congr
    intro t
    change diagramInterior q (e p.1, e p.2) (e r.1, e r.2) *
      diagramConnector q (e r.1, e r.2) (e t.1, e t.2) *
      diagramReverseIterate q (e y) n (e t.1, e t.2) = _
    rw [diagramInterior_apply_equiv q e hq, diagramConnector_apply_equiv q e hq, ih]

/-- Moving an unmarked transfer across the cut replaces the forward step by
one backward step, by Tonelli alone. -/
theorem diagramIterate_connector_reverse_succ (q : Sym2 V → unitInterval)
    (x y : V) (i j : ℕ) :
    (∑' p, ∑' s, diagramIterate q x (i + 1) p * diagramConnector q p s *
      diagramReverseIterate q y j s) =
      ∑' p, ∑' s, diagramIterate q x i p * diagramConnector q p s *
        diagramReverseIterate q y (j + 1) s := by
  classical
  simp only [diagramIterate, diagramTransfer, diagramReverseIterate_succ]
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  simp_rw [← ENNReal.tsum_mul_right]
  calc
    _ = ∑' r, ∑' t, ∑' p, ∑' s,
        (diagramIterate q x i r * (diagramConnector q r t * diagramInterior q t p)) *
          diagramConnector q p s * diagramReverseIterate q y j s := by
      simpa only [ENNReal.tsum_prod'] using
        (ENNReal.tsum_comm (f := fun (p : (V × V) × (V × V))
            (r : (V × V) × (V × V)) =>
          (diagramIterate q x i r.1 *
            (diagramConnector q r.1 r.2 * diagramInterior q r.2 p.1)) *
            diagramConnector q p.1 p.2 * diagramReverseIterate q y j p.2))
    _ = _ := by
      apply tsum_congr
      intro p
      apply tsum_congr
      intro s
      apply tsum_congr
      intro r
      apply tsum_congr
      intro t
      ac_rfl

/-- Every connector position gives an exact forward/backward cut of the
actual unweighted diagram. -/
theorem laceDiagram_eq_tsum_connector_cut (q : Sym2 V → unitInterval)
    (x y : V) (i j : ℕ) :
    laceDiagram q (i + j) x y =
      ∑' p, ∑' s, diagramIterate q x i p * diagramConnector q p s *
        diagramReverseIterate q y j s := by
  classical
  induction j generalizing i with
  | zero =>
    simp only [Nat.add_zero, laceDiagram, diagramTerminal, diagramReverseIterate_zero]
    simp_rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro p
    apply tsum_congr
    intro s
    ac_rfl
  | succ j ih =>
    rw [show i + (j + 1) = (i + 1) + j by omega, ih,
      diagramIterate_connector_reverse_succ]

section Translation

variable {G : Type*} [AddGroup G]

/-- Translation covariance of the actual backward iterate. -/
theorem diagramReverseIterate_add_right (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (y : G) (n : ℕ) (p : G × G) (g : G) :
    diagramReverseIterate q (y + g) n (p.1 + g, p.2 + g) =
      diagramReverseIterate q y n p := by
  apply diagramReverseIterate_apply_equiv q (Equiv.addRight g)
  intro a
  induction a using Sym2.ind with
  | _ u v => exact hq u v g

/-- At a marked connector, translating the suffix by its endpoint isolates
the exact common-translation core. `true` selects the second coordinate. -/
theorem markedConnector_mass_eq_tsum_core
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (ψ : AddChar G Circle) (ε : Bool) (x : G) (i j : ℕ) :
    let c : G × G → G := fun p => if ε then p.2 else p.1
    let h : G → ℝ≥0∞ := fun z => ENNReal.ofReal (1 - (ψ z : ℂ).re)
    (∑' y, ∑' p, ∑' s, diagramIterate q x i p * h (c s - c p) *
      diagramConnector q p s * diagramReverseIterate q y j s) =
      ∑' p, ∑' r, diagramIterate q x i p * diagramReverseIterate q 0 j r *
        (∑' y, h (c r + y - c p) * diagramConnector q p (r.1 + y, r.2 + y)) := by
  classical
  dsimp only
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro p
  calc
    _ = ∑' y, ∑' r : G × G,
        diagramIterate q x i p *
          ENNReal.ofReal (1 - (ψ ((if ε then r.2 else r.1) + y -
            (if ε then p.2 else p.1)) : ℂ).re) *
          diagramConnector q p (r.1 + y, r.2 + y) * diagramReverseIterate q 0 j r := by
      apply tsum_congr
      intro y
      rw [← (Equiv.prodCongr (Equiv.addRight y) (Equiv.addRight y)).tsum_eq]
      apply tsum_congr
      intro r
      change diagramIterate q x i p *
        ENNReal.ofReal (1 - (ψ ((if ε then r.2 + y else r.1 + y) -
          (if ε then p.2 else p.1)) : ℂ).re) *
        diagramConnector q p (r.1 + y, r.2 + y) *
        diagramReverseIterate q y j (r.1 + y, r.2 + y) = _
      have hG := diagramReverseIterate_add_right q hq 0 j r y
      simp only [zero_add] at hG
      rw [hG]
      cases ε <;> rfl
    _ = _ := by
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro r
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro y
      ac_rfl

/-- An inserted connector mark has separate forward and backward geometric
factors. The only marked norm is the displayed local translated connector. -/
theorem markedConnector_mass_le_geometric
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (ψ : AddChar G Circle) (ε : Bool) (x : G) (i j : ℕ) (ρ σ m : ℝ≥0∞)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hσ : ∀ p, (∑' s, ∑' r, diagramInterior q s r * diagramConnector q r p) ≤ σ)
    (hcore : ∀ p r : G × G, (∑' y,
      ENNReal.ofReal (1 - (ψ ((if ε then r.2 else r.1) + y -
        (if ε then p.2 else p.1)) : ℂ).re) *
        diagramConnector q p (r.1 + y, r.2 + y)) ≤ m) :
    let c : G × G → G := fun p => if ε then p.2 else p.1
    let h : G → ℝ≥0∞ := fun z => ENNReal.ofReal (1 - (ψ z : ℂ).re)
    (∑' y, ∑' p, ∑' s, diagramIterate q x i p * h (c s - c p) *
      diagramConnector q p s * diagramReverseIterate q y j s) ≤
      (∑' p, diagramInitial q x p) *
        (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) * ρ ^ i * σ ^ j * m := by
  classical
  dsimp only
  rw [markedConnector_mass_eq_tsum_core q hq ψ ε x i j]
  calc
    _ ≤ ∑' p, ∑' r, diagramIterate q x i p * diagramReverseIterate q 0 j r * m :=
      ENNReal.tsum_le_tsum fun p => ENNReal.tsum_le_tsum fun r =>
        mul_le_mul' le_rfl (hcore p r)
    _ = (∑' p, diagramIterate q x i p) * (∑' r, diagramReverseIterate q 0 j r) * m := by
      simp only [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
    _ ≤ ((∑' p, diagramInitial q x p) * ρ ^ i) *
        ((∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) * σ ^ j) * m :=
      mul_le_mul' (mul_le_mul' (diagramIterate_mass_le_geometric q x ρ hρ i)
        (diagramReverseIterate_mass_le_geometric q 0 σ hσ j)) le_rfl
    _ = _ := by ac_rfl

end Translation

end PercLib.Percolation.Bond.Lace
