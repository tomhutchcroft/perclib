/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original proofs sharpening the transfer estimate of Heydenreich and van der
Hofstad (2017), Section 7.5, by retaining the excluded joining diagonal.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.TriangleBounds
public import PercLib.Percolation.Bond.Lace.Transport
public import PercLib.Percolation.Bond.ConnectionKernel

/-!
# Transfer norms with the excluded joining diagonal

The first part of the transfer retains the actual deleted connector. The
second part retains the off-diagonal joining connection. Under translations
this gives the bound `Δ * (M + Moff)`, instead of replacing both terms by `Δ * M`.
All sums take values in the extended nonnegative reals.
-/

@[expose] public section
noncomputable section

open scoped ENNReal Classical

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- Removing the joining diagonal subtracts an explicitly identified
nonnegative contribution, expressed without extended-real subtraction. -/
theorem weighted_tau_mass_eq_diagonal_add_offDiagonal
    (q : Sym2 V → unitInterval) (f : V → V → ℝ≥0∞) :
    (∑' z, ∑' t, f z t * tau q z t) =
      (∑' z, f z z) + ∑' z, ∑' t, f z t * offDiagonal (tau q) z t := by
  have hrow (z : V) : (∑' t, f z t * tau q z t) =
      f z z + ∑' t, f z t * offDiagonal (tau q) z t := by
    rw [ENNReal.tsum_eq_add_tsum_ite z]
    simp only [tau_self, mul_one]
    congr 1
    apply tsum_congr
    intro t
    by_cases ht : t = z <;> simp [offDiagonal, ht]
  simp_rw [hrow, ENNReal.tsum_add]

/-- Exact row decomposition of the two interior geometries. -/
theorem diagramInterior_mass_eq (q : Sym2 V → unitInterval) (p : V × V) :
    (∑' r, diagramInterior q p r) =
      tau q p.1 p.2 * (∑' u, ∑' w, tau q p.1 u * tau q u w * tau q w p.2) +
      ∑' u, ∑' w, tau q p.1 u * offDiagonal (tau q) p.2 w * tau q w p.1 * tau q w u := by
  rw [ENNReal.tsum_prod']
  simp only [diagramInterior, ENNReal.tsum_add]
  congr 1
  · rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro u
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro w
    rw [tau_comm q p.2 w, tau_comm q w u]
    ac_rfl
  · rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro u
    simp only [tsum_ite_eq', ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro w
    by_cases hw : w = p.2 <;> simp [offDiagonal, hw, mul_assoc]

/-- Exact transfer-row decomposition, retaining the deleted connector in both
parts and the excluded joining diagonal in the second part. -/
theorem diagramTransfer_mass_eq (q : Sym2 V → unitInterval) (p : V × V) :
    (∑' r, diagramTransfer q p r) =
      (∑' s : V × V, diagramConnector q p s * tau q s.1 s.2 *
        (∑' u, ∑' w, tau q s.1 u * tau q u w * tau q w s.2)) +
      ∑' s : V × V, ∑' u, ∑' w, diagramConnector q p s * tau q s.1 u *
        offDiagonal (tau q) s.2 w * tau q w s.1 * tau q w u := by
  unfold diagramTransfer
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left, diagramInterior_mass_eq, mul_add]
  rw [ENNReal.tsum_add]
  congr 1
  · apply tsum_congr
    intro s
    rw [mul_assoc]
  · apply tsum_congr
    intro s
    simp_rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro u
    apply tsum_congr
    intro w
    ac_rfl

/-- Diagonal triangle bounds also control open triangles, by positivity of
the connection kernel. -/
theorem open_triangle_le_of_diagonal_bound [Countable V]
    (q : Sym2 V → unitInterval) (Δ : ℝ≥0∞)
    (hΔ : ∀ x, (∑' u, ∑' v, tau q x u * tau q u v * tau q v x) ≤ Δ) (x y : V) :
    (∑' u, ∑' v, tau q x u * tau q u v * tau q v y) ≤ Δ := by
  have hs := (triangle_sq_le q x y).trans (mul_le_mul' (hΔ x) (hΔ y))
  have hr := ENNReal.rpow_le_rpow hs (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hroot (z : ℝ≥0∞) : (z ^ 2) ^ (1 / 2 : ℝ) = z := by
    simpa [one_div] using ENNReal.pow_rpow_inv_natCast (n := 2) (by norm_num) z
  rw [← sq, hroot, hroot] at hr
  exact hr

/-- The first transfer geometry costs the triangle bound times the exact
deleted-connector mass. The remaining geometry is kept explicitly. -/
theorem diagramTransfer_mass_le_deleted_add [Countable V]
    (q : Sym2 V → unitInterval) (p : V × V) (Δ : ℝ≥0∞)
    (hΔ : ∀ x, (∑' u, ∑' v, tau q x u * tau q u v * tau q v x) ≤ Δ) :
    (∑' r, diagramTransfer q p r) ≤
      (∑' s : V × V, diagramConnector q p s * tau q s.1 s.2) * Δ +
      ∑' s : V × V, ∑' u, ∑' w, diagramConnector q p s * tau q s.1 u *
        offDiagonal (tau q) s.2 w * tau q w s.1 * tau q w u := by
  rw [diagramTransfer_mass_eq]
  refine add_le_add ?_ le_rfl
  calc
    _ ≤ ∑' s : V × V, diagramConnector q p s * tau q s.1 s.2 * Δ :=
      ENNReal.tsum_le_tsum fun s =>
        mul_le_mul_right (open_triangle_le_of_diagonal_bound q Δ hΔ s.1 s.2) _
    _ = _ := ENNReal.tsum_mul_right

section Translation

variable {G : Type*} [AddCommGroup G]

private theorem tau_add_right (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (x y g : G) :
    tau q (x + g) (y + g) = tau q x y := by
  apply tau_eq_of_map_law (Equiv.addRight g)
  apply PercLib.Probability.prodBernoulli_map_image_sym2_invariant
  intro a
  induction a using Sym2.ind with
  | _ u v => exact hq u v g

/-- All diagonal triangles equal the triangle at zero under translation
invariance of the profile. -/
theorem diagonal_triangle_eq_rooted (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (x : G) :
    (∑' u, ∑' v, tau q x u * tau q u v * tau q v x) =
      ∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0 := by
  rw [← (Equiv.addRight x).tsum_eq]
  apply tsum_congr
  intro u
  rw [← (Equiv.addRight x).tsum_eq]
  apply tsum_congr
  intro v
  change tau q x (u + x) * tau q (u + x) (v + x) * tau q (v + x) x = _
  have hleft := tau_add_right q hq 0 u x
  have hright := tau_add_right q hq v 0 x
  simp only [zero_add] at hleft hright
  rw [hleft, hright, tau_add_right q hq]

omit [AddCommGroup G] in
private theorem offDiagonal_tau_comm (q : Sym2 G → unitInterval) (x y : G) :
    offDiagonal (tau q) x y = offDiagonal (tau q) y x := by
  by_cases h : x = y
  · subst y
    rfl
  · simp [offDiagonal, h, Ne.symm h, tau_comm q x y]

private theorem tsum_four_swap {A B C D : Type*} (f : A → B → C → D → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, ∑' d, f a b c d) =
      ∑' c, ∑' d, ∑' a, ∑' b, f a b c d := by
  have h := ENNReal.tsum_comm (f := fun p : A × B => fun r : C × D =>
    f p.1 p.2 r.1 r.2)
  simpa only [ENNReal.tsum_prod'] using h

/-- The second interior geometry has an off-diagonal convolution norm. The
excluded joining diagonal is retained throughout the estimate. -/
theorem diagramTransfer_second_mass_le_of_add_right
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (p : G × G) (Moff : ℝ≥0∞)
    (hMoff : ∀ s h, (∑' z, ∑' t, tau q s z *
      (∑' v, offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) h v * tau q v t) *
          offDiagonal (tau q) z t) ≤ Moff) :
    (∑' s : G × G, ∑' u, ∑' w, diagramConnector q p s * tau q s.1 u *
      offDiagonal (tau q) s.2 w * tau q w s.1 * tau q w u) ≤
      (∑' u, ∑' w, tau q 0 u * tau q u w * tau q w 0) * Moff := by
  let T : G → G → ℝ≥0∞ := fun h t => ∑' v,
    offDiagonal (fun a b : G => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) h v * tau q v t
  have hinner (w : G) :
      (∑' z, ∑' t, tau q p.1 z * T p.2 t * offDiagonal (tau q) t (w + z)) ≤ Moff := by
    calc
      _ = ∑' z, ∑' t, tau q (p.1 + w) (z + w) * T p.2 t *
          offDiagonal (tau q) (z + w) t := by
        apply tsum_congr
        intro z
        apply tsum_congr
        intro t
        rw [tau_add_right q hq, offDiagonal_tau_comm, add_comm w z]
      _ = ∑' z, ∑' t, tau q (p.1 + w) z * T p.2 t * offDiagonal (tau q) z t := by
        simpa only [Equiv.coe_addRight] using (Equiv.addRight w).tsum_eq
          (fun z => ∑' t, tau q (p.1 + w) z * T p.2 t * offDiagonal (tau q) z t)
      _ ≤ Moff := hMoff (p.1 + w) p.2
  calc
    _ ≤ ∑' z, ∑' t, ∑' u, ∑' w,
        tau q p.1 z * T p.2 t * tau q z u * offDiagonal (tau q) t w *
          tau q w z * tau q w u := by
      rw [ENNReal.tsum_prod']
      apply ENNReal.tsum_le_tsum
      intro z
      apply ENNReal.tsum_le_tsum
      intro t
      apply ENNReal.tsum_le_tsum
      intro u
      apply ENNReal.tsum_le_tsum
      intro w
      exact mul_le_mul' (mul_le_mul' (mul_le_mul'
        (mul_le_mul' (diagramConnector_le q p (z, t)) le_rfl) le_rfl) le_rfl) le_rfl
    _ = ∑' z, ∑' t, ∑' u, ∑' w,
        (tau q 0 u * tau q u w * tau q w 0) *
          (tau q p.1 z * T p.2 t * offDiagonal (tau q) t (w + z)) := by
      apply tsum_congr
      intro z
      apply tsum_congr
      intro t
      rw [← (Equiv.addRight z).tsum_eq]
      apply tsum_congr
      intro u
      rw [← (Equiv.addRight z).tsum_eq]
      apply tsum_congr
      intro w
      change tau q p.1 z * T p.2 t * tau q z (u + z) *
        offDiagonal (tau q) t (w + z) * tau q (w + z) z *
          tau q (w + z) (u + z) = _
      have hleft := tau_add_right q hq 0 u z
      have hright := tau_add_right q hq w 0 z
      simp only [zero_add] at hleft hright
      rw [hleft, hright, tau_add_right q hq, tau_comm q w u]
      ac_rfl
    _ = ∑' u, ∑' w, (tau q 0 u * tau q u w * tau q w 0) *
        (∑' z, ∑' t, tau q p.1 z * T p.2 t * offDiagonal (tau q) t (w + z)) := by
      rw [tsum_four_swap]
      simp_rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' u, ∑' w, (tau q 0 u * tau q u w * tau q w 0) * Moff :=
      ENNReal.tsum_le_tsum fun _ => ENNReal.tsum_le_tsum fun w =>
        mul_le_mul_right (hinner w) _
    _ = _ := by simp only [ENNReal.tsum_mul_right]

/-- The transfer estimate keeps the exact deleted first-geometry mass and
the smaller off-diagonal norm in the second geometry. -/
theorem diagramTransfer_mass_le_deleted_of_add_right [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (p : G × G) (Δ Md Moff : ℝ≥0∞)
    (hΔ : (∑' u, ∑' w, tau q 0 u * tau q u w * tau q w 0) ≤ Δ)
    (hMd : (∑' s : G × G, diagramConnector q p s * tau q s.1 s.2) ≤ Md)
    (hMoff : ∀ s h, (∑' z, ∑' t, tau q s z *
      (∑' v, offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) h v * tau q v t) *
          offDiagonal (tau q) z t) ≤ Moff) :
    (∑' r, diagramTransfer q p r) ≤ Δ * (Md + Moff) := by
  have hdiag (x : G) : (∑' u, ∑' v, tau q x u * tau q u v * tau q v x) ≤ Δ := by
    rw [diagonal_triangle_eq_rooted q hq]
    exact hΔ
  calc
    _ ≤ (∑' s : G × G, diagramConnector q p s * tau q s.1 s.2) * Δ +
        ∑' s : G × G, ∑' u, ∑' w, diagramConnector q p s * tau q s.1 u *
          offDiagonal (tau q) s.2 w * tau q w s.1 * tau q w u :=
      diagramTransfer_mass_le_deleted_add q p Δ hdiag
    _ ≤ Md * Δ + Δ * Moff := add_le_add (mul_le_mul' hMd le_rfl)
      ((diagramTransfer_second_mass_le_of_add_right q hq p Moff hMoff).trans
        (mul_le_mul' hΔ le_rfl))
    _ = _ := by rw [mul_add, mul_comm Md Δ]

/-- Dropping deletion only in the first mass gives `Δ * (M + Moff)`, with no
factor two from counting the excluded joining diagonal a second time. -/
theorem diagramTransfer_mass_le_of_add_right [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (Δ M Moff : ℝ≥0∞)
    (hΔ : (∑' u, ∑' w, tau q 0 u * tau q u w * tau q w 0) ≤ Δ)
    (hM : ∀ s h, (∑' z, ∑' t, tau q s z *
      (∑' v, offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) h v * tau q v t) * tau q z t) ≤ M)
    (hMoff : ∀ s h, (∑' z, ∑' t, tau q s z *
      (∑' v, offDiagonal (fun a b : G =>
        (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) h v * tau q v t) *
          offDiagonal (tau q) z t) ≤ Moff) (p : G × G) :
    (∑' r, diagramTransfer q p r) ≤ Δ * (M + Moff) := by
  apply diagramTransfer_mass_le_deleted_of_add_right q hq p Δ M Moff hΔ _ hMoff
  calc
    _ ≤ ∑' s : G × G, (tau q p.1 s.1 *
        ∑' v, offDiagonal (fun a b : G =>
          (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) p.2 v * tau q v s.2) * tau q s.1 s.2 :=
      ENNReal.tsum_le_tsum fun s => mul_le_mul' (diagramConnector_le q p s) le_rfl
    _ = ∑' z, ∑' t, (tau q p.1 z *
        ∑' v, offDiagonal (fun a b : G =>
          (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) p.2 v * tau q v t) * tau q z t :=
      ENNReal.tsum_prod'
    _ ≤ M := hM p.1 p.2

end Translation

end PercLib.Percolation.Bond.Lace
