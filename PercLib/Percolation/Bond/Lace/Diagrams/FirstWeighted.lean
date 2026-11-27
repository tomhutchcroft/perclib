/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original refinements of the first weighted lace diagram. Mathematical reference:
Heydenreich and van der Hofstad (2017), Section 7.5.3.
No upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.WeightedCoefficientBounds

/-!
# Removing the trivial first weighted diagram

## Main results

The certain initial diagonal and the fully collapsed terminal triangle are
split off exactly. The remaining initial mass is smaller than the nontrivial
full triangle mass. Bounds retain the actual forward and backward deleted
connector masses before any uniform scalar simplification.
-/

@[expose] public section
noncomputable section

open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {G : Type*} [AddCommGroup G]

open scoped Classical in
omit [AddCommGroup G] in
/-- A weighted initial row splits into its certain diagonal and the row
whose second coordinate differs from the root. -/
theorem tsum_diagramInitial_mul_eq_diagonal_add
    (q : Sym2 G → unitInterval) (x : G) (f : (G × G) → ℝ≥0∞) :
    (∑' p, diagramInitial q x p * f p) = f (x, x) +
      ∑' p, (if p.2 = x then 0 else diagramInitial q x p) * f p := by
  classical
  have hp (p : G × G) : diagramInitial q x p * f p =
      (if p = (x, x) then f (x, x) else 0) +
        (if p.2 = x then 0 else diagramInitial q x p) * f p := by
    rcases p with ⟨s, t⟩
    by_cases ht : t = x <;> by_cases hs : s = x <;>
      simp [diagramInitial, ht, hs]
  simp_rw [hp, ENNReal.tsum_add]
  simp

open scoped Classical in
/-- The nontrivial terminal triangle is the nontrivial initial mass plus
one off-diagonal bubble. This identity uses no extended-real subtraction. -/
theorem nontrivial_triangle_mass_eq_initial_add_bubble
    (q : Sym2 G → unitInterval) :
    (∑' p : G × G, if p = (0, 0) then 0 else
      tau q 0 p.1 * tau q p.1 p.2 * tau q p.2 0) =
      (∑' p : G × G, if p.2 = 0 then 0 else diagramInitial q 0 p) +
        ∑' z, if z = 0 then 0 else tau q 0 z ^ 2 := by
  classical
  have hp (p : G × G) :
      (if p = (0, 0) then 0 else tau q 0 p.1 * tau q p.1 p.2 * tau q p.2 0) =
      (if p.2 = 0 then 0 else diagramInitial q 0 p) +
        if p.2 = 0 then (if p.1 = 0 then 0 else tau q 0 p.1 ^ 2) else 0 := by
    rcases p with ⟨s, t⟩
    by_cases ht : t = 0 <;> by_cases hs : s = 0 <;>
      simp [diagramInitial, ht, hs, tau_self, tau_comm q t 0, tau_comm q s 0, pow_two,
        mul_comm, mul_assoc]
  simp_rw [hp, ENNReal.tsum_add]
  congr 1
  rw [ENNReal.tsum_prod']
  simp

open scoped Classical in
/-- Each nonzero initial row contains two distinct bubble contributions. -/
theorem two_mul_offDiagonal_bubble_le_nontrivial_initial
    (q : Sym2 G → unitInterval) :
    2 * (∑' z, if z = 0 then 0 else tau q 0 z ^ 2) ≤
      ∑' p : G × G, if p.2 = 0 then 0 else diagramInitial q 0 p := by
  classical
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro z
  by_cases hz : z = 0
  · simp [hz]
  · simp only [hz, ite_false, diagramInitial]
    have h := ENNReal.sum_le_tsum ({0, z} : Finset G)
      (f := fun s => tau q 0 s * tau q 0 z * tau q s z)
    simpa only [Finset.sum_pair (Ne.symm hz), tau_self, one_mul, mul_one, pow_two,
      two_mul] using h

open scoped Classical in
/-- The exact nontrivial initial mass controls the nontrivial full triangle
with factor three halves. No finiteness premise is needed. -/
theorem nontrivial_triangle_mass_le_three_halves_initial
    (q : Sym2 G → unitInterval) :
    (∑' p : G × G, if p = (0, 0) then 0 else
      tau q 0 p.1 * tau q p.1 p.2 * tau q p.2 0) ≤
      (3 / 2 : ℝ≥0∞) * (∑' p : G × G, if p.2 = 0 then 0 else diagramInitial q 0 p) := by
  classical
  let a := ∑' p : G × G, if p.2 = 0 then 0 else diagramInitial q 0 p
  let b := ∑' z, if z = 0 then 0 else tau q 0 z ^ 2
  have hb : b ≤ (1 / 2 : ℝ≥0∞) * a := by
    calc
      b = (1 / 2 : ℝ≥0∞) * (2 * b) := by
        rw [one_div, ← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
          one_mul]
      _ ≤ _ := mul_le_mul' le_rfl (two_mul_offDiagonal_bubble_le_nontrivial_initial q)
  rw [nontrivial_triangle_mass_eq_initial_add_bubble]
  change a + b ≤ (3 / 2 : ℝ≥0∞) * a
  calc
    _ ≤ a + (1 / 2 : ℝ≥0∞) * a := add_le_add le_rfl hb
    _ = _ := by
      rw [← one_add_mul]
      congr 1
      calc
        (1 : ℝ≥0∞) + 1 / 2 = 2 / 2 + 1 / 2 := by
          rw [ENNReal.div_self two_ne_zero ENNReal.ofNat_ne_top]
        _ = _ := by rw [← ENNReal.add_div]; norm_num

open scoped Classical in
/-- The necessarily nonzero second initial coordinate permits the first-step
bound without paying for any diagonal term. -/
theorem nontrivial_initial_mass_le_continuation_triangle [Countable G]
    (q : Sym2 G → unitInterval) :
    (∑' p : G × G, if p.2 = 0 then 0 else diagramInitial q 0 p) ≤
      ∑' s, ∑' t, tau q 0 s *
        (∑' v, offDiagonal (fun a b : G =>
          (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 v * tau q v t) * tau q s t := by
  classical
  rw [ENNReal.tsum_prod']
  apply ENNReal.tsum_le_tsum
  intro s
  apply ENNReal.tsum_le_tsum
  intro t
  by_cases ht : t = 0
  · simp [ht]
  · simp only [ht, ite_false, diagramInitial]
    exact mul_le_mul' (mul_le_mul' le_rfl
      (tau_le_tsum_offDiagonal_mul_tau q (Ne.symm ht))) le_rfl

/-- The fully collapsed first diagram is bounded by the weighted pair at
shift zero, with constant one; its connector still retains bond deletion. -/
theorem tsum_weight_mul_diagonal_connector_le_weightedPair
    (q : Sym2 G → unitInterval) (w : G → ℝ≥0∞) :
    (∑' y, w y * diagramConnector q (0, 0) (y, y)) ≤ diagramWeightedPair q w 0 := by
  classical
  unfold diagramWeightedPair
  apply ENNReal.tsum_le_tsum
  intro y
  refine (mul_le_mul' le_rfl (diagramConnector_le q (0, 0) (y, y))).trans_eq ?_
  simp only [add_zero]
  ac_rfl

private theorem tsum_reverse_zero_eq_triangle (q : Sym2 G → unitInterval) :
    (∑' s, diagramReverseIterate q 0 0 s) =
      ∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0 := by
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro u
  apply tsum_congr
  intro v
  simp only [diagramReverseIterate_zero, tau_comm q u 0]
  ac_rfl

private theorem tsum_row_connector_mark_le
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (F : (G × G) → ℝ≥0∞) (w : G → ℝ≥0∞) :
    (∑' y, ∑' p, ∑' s, F p * (w (s.2 - p.2) * diagramConnector q p s) *
      diagramReverseIterate q y 0 s) ≤
      (∑' p, F p) * (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) *
        ⨆ a, diagramWeightedPair q w a := by
  classical
  calc
    _ = ∑' p, ∑' r, F p * diagramReverseIterate q 0 0 r *
        diagramMarkedConnectorCore q w true p r := by
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro p
      calc
        _ = ∑' y, ∑' r : G × G, F p *
            (w (r.2 + y - p.2) * diagramConnector q p (r.1 + y, r.2 + y)) *
              diagramReverseIterate q 0 0 r := by
          apply tsum_congr
          intro y
          rw [← (Equiv.prodCongr (Equiv.addRight y) (Equiv.addRight y)).tsum_eq]
          apply tsum_congr
          intro r
          change F p * (w (r.2 + y - p.2) * diagramConnector q p (r.1 + y, r.2 + y)) *
            diagramReverseIterate q y 0 (r.1 + y, r.2 + y) = _
          have hG := diagramReverseIterate_add_right q hq 0 0 r y
          simp only [zero_add] at hG
          rw [hG]
        _ = _ := by
          rw [ENNReal.tsum_comm]
          apply tsum_congr
          intro r
          simp only [diagramMarkedConnectorCore_true]
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro y
          ac_rfl
    _ ≤ ∑' p, ∑' r, F p * diagramReverseIterate q 0 0 r *
        (⨆ a, diagramWeightedPair q w a) :=
      ENNReal.tsum_le_tsum fun p => ENNReal.tsum_le_tsum fun r =>
        mul_le_mul' le_rfl (diagramMarkedConnectorCore_true_le_iSup q hq w p r)
    _ = _ := by
      simp only [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left,
        tsum_reverse_zero_eq_triangle]

private theorem tsum_row_terminal_mark_le [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (F : (G × G) → ℝ≥0∞) (w : G → ℝ≥0∞) (hw : w 0 = 0) (Md : ℝ≥0∞)
    (hMd : ∀ p, (∑' s : G × G, diagramConnector q p s * tau q s.1 s.2) ≤ Md) :
    (∑' y, ∑' p, ∑' s, F p * diagramConnector q p s *
      diagramReverseIterate q y 0 s * w (y - s.2)) ≤
      (∑' p, F p) * Md * ⨆ a, diagramWeightedPair q w a := by
  classical
  calc
    _ = ∑' p, F p * diagramMarkedTerminalCore q w true p := by
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro p
      rw [ENNReal.tsum_comm]
      simp only [diagramMarkedTerminalCore, diagramReverseIterate_zero, ite_true]
      simp_rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro s
      apply tsum_congr
      intro y
      ac_rfl
    _ ≤ ∑' p, F p * (Md * (⨆ a, diagramWeightedPair q w a)) :=
      ENNReal.tsum_le_tsum fun p => mul_le_mul' le_rfl
        ((diagramMarkedTerminalCore_le_deleted_mass q hq w hw true p).trans
          (mul_le_mul' (hMd p) le_rfl))
    _ = _ := by rw [ENNReal.tsum_mul_right, mul_assoc]

open scoped Classical in
/-- The nontrivial initial piece retains its own mass in both the middle
and terminal marks. The terminal cost is therefore quadratic in small masses. -/
theorem first_diagram_nontrivial_initial_weight_le [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (ψ : AddChar G Circle) (Md Mr : ℝ≥0∞)
    (hMd : ∀ p, (∑' s : G × G, diagramConnector q p s * tau q s.1 s.2) ≤ Md)
    (hMr : ∀ r, (∑' t : G × G, diagramConnector q t r * tau q t.1 t.2) ≤ Mr) :
    let w : G → ℝ≥0∞ := fun z => ENNReal.ofReal (1 - (ψ z : ℂ).re)
    let F : (G × G) → ℝ≥0∞ := fun p => if p.2 = 0 then 0 else diagramInitial q 0 p
    let a := ∑' p, F p
    let Δ := ∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0
    (∑' y, ∑' p, ∑' s, w y * (F p * diagramConnector q p s *
      diagramReverseIterate q y 0 s)) ≤
      3 * (Δ * Mr + a * Δ + a * Md) * ⨆ z, diagramWeightedPair q w z := by
  classical
  dsimp only
  let w : G → ℝ≥0∞ := fun z => ENNReal.ofReal (1 - (ψ z : ℂ).re)
  let F : (G × G) → ℝ≥0∞ := fun p => if p.2 = 0 then 0 else diagramInitial q 0 p
  let Δ := ∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0
  let W := ⨆ z, diagramWeightedPair q w z
  have hw : w 0 = 0 := by simp [w]
  have hI : (∑' y, ∑' p, ∑' s,
      F p * (w p.2 * diagramConnector q p s) * diagramReverseIterate q y 0 s) ≤
        Δ * Mr * W := by
    calc
      _ = ∑' y, ∑' p, ∑' s, diagramInitial q 0 p *
          (w (p.2 - 0) * diagramConnector q p s) * diagramReverseIterate q y 0 s := by
        apply tsum_congr
        intro y
        apply tsum_congr
        intro p
        apply tsum_congr
        intro s
        by_cases hp : p.2 = 0 <;> simp [F, hp, hw]
      _ = _ := markedInitial_mass_eq_tsum_core q hq w 0 0
      _ ≤ Δ * Mr * W := by
        calc
          _ ≤ ∑' r, diagramReverseIterate q 0 0 r * (Mr * W) :=
            ENNReal.tsum_le_tsum fun r => mul_le_mul' le_rfl
              ((diagramMarkedInitialCore_le_reverse_deleted_mass q hq w hw 0 r).trans
                (mul_le_mul' (hMr r) le_rfl))
          _ = _ := by
            rw [ENNReal.tsum_mul_right, tsum_reverse_zero_eq_triangle]
            change Δ * (Mr * W) = Δ * Mr * W
            ac_rfl
  have hC := tsum_row_connector_mark_le q hq F w
  have hT := tsum_row_terminal_mark_le q hq F w hw Md hMd
  have hroute (p s : G × G) (y : G) :
      w y ≤ 3 * (w p.2 + w (s.2 - p.2) + w (y - s.2)) := by
    simpa [w] using
      character_weight_chain_route_le ψ 0 0 y (fun _ => p.2) (fun _ => s.2)
  calc
    _ ≤ ∑' y, ∑' p, ∑' s,
        (3 * (w p.2 + w (s.2 - p.2) + w (y - s.2))) *
          (F p * diagramConnector q p s * diagramReverseIterate q y 0 s) :=
      ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun p =>
        ENNReal.tsum_le_tsum fun s => mul_le_mul' (hroute p s y) le_rfl
    _ = 3 * ((∑' y, ∑' p, ∑' s, F p *
          (w p.2 * diagramConnector q p s) * diagramReverseIterate q y 0 s) +
        (∑' y, ∑' p, ∑' s, F p *
          (w (s.2 - p.2) * diagramConnector q p s) * diagramReverseIterate q y 0 s) +
        (∑' y, ∑' p, ∑' s, F p * diagramConnector q p s *
          diagramReverseIterate q y 0 s * w (y - s.2))) := by
      simp_rw [← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro y
      apply tsum_congr
      intro p
      apply tsum_congr
      intro s
      ring
    _ ≤ 3 * ((Δ * Mr * W) + ((∑' p, F p) * Δ * W) + ((∑' p, F p) * Md * W)) :=
      mul_le_mul' le_rfl (add_le_add (add_le_add hI hC) hT)
    _ = _ := by change _ = 3 * (Δ * Mr + (∑' p, F p) * Δ + (∑' p, F p) * Md) * W; ring

open scoped Classical in
private theorem first_diagram_nontrivial_terminal_connector_mark_le
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) :
    (∑' y, ∑' s : G × G, (if s = (y, y) then 0 else
      diagramConnector q (0, 0) s * diagramReverseIterate q y 0 s) * w s.2) ≤
      (∑' p : G × G, if p = (0, 0) then 0 else
        tau q 0 p.1 * tau q p.1 p.2 * tau q p.2 0) *
          ⨆ a, diagramWeightedPair q w a := by
  classical
  let T : G → ℝ≥0∞ := fun t => ∑' v, offDiagonal (fun a b : G =>
    (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 v * tau q v t
  let Γ : G → G → ℝ≥0∞ := fun a b => if (a, b) = (0, 0) then 0 else
    tau q 0 a * tau q a b * tau q b 0
  rw [ENNReal.tsum_comm, ENNReal.tsum_prod', ENNReal.tsum_comm]
  calc
    _ ≤ ∑' t, ∑' a, ∑' b, Γ a b * (w t * T t * tau q 0 (t + a)) := by
      apply ENNReal.tsum_le_tsum
      intro t
      rw [← (Equiv.addRight t).tsum_eq]
      apply ENNReal.tsum_le_tsum
      intro a
      rw [← (Equiv.addRight t).tsum_eq]
      apply ENNReal.tsum_le_tsum
      intro b
      change (if (a + t, t) = (b + t, b + t) then 0 else
        diagramConnector q (0, 0) (a + t, t) *
          diagramReverseIterate q (b + t) 0 (a + t, t)) * w t ≤ _
      have he : (a + t, t) = (b + t, b + t) ↔ (a, b) = (0, 0) := by
        constructor
        · intro h
          have hb : b = 0 := add_right_cancel
            (show b + t = 0 + t from by simpa using (congrArg Prod.snd h).symm)
          subst b
          have ha : a = 0 := add_right_cancel
            (show a + t = 0 + t from by simpa using congrArg Prod.fst h)
          simp [ha]
        · rintro h
          have ha := congrArg Prod.fst h
          have hb := congrArg Prod.snd h
          simp_all
      by_cases hab : (a, b) = (0, 0)
      · simp [he, hab, Γ]
      · have hG := diagramReverseIterate_add_right q hq b 0 (a, 0) t
        simp only [zero_add] at hG
        rw [ite_eq_right (mt he.mp hab), hG]
        refine (mul_le_mul' (mul_le_mul' (diagramConnector_le q (0, 0) (a + t, t))
          le_rfl) le_rfl).trans_eq ?_
        simp only [Γ, hab, ite_false, diagramReverseIterate_zero, tau_comm q a 0,
          tau_comm q 0 b, add_comm a t]
        change (_ * T t * _) * _ = _
        ac_rfl
    _ = ∑' a, ∑' b, Γ a b * diagramWeightedPair q w a := by
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro a
      rw [ENNReal.tsum_comm]
      simp only [diagramWeightedPair, T, ENNReal.tsum_mul_left]
    _ ≤ ∑' a, ∑' b, Γ a b * (⨆ z, diagramWeightedPair q w z) :=
      ENNReal.tsum_le_tsum fun a => ENNReal.tsum_le_tsum fun _ =>
        mul_le_mul' le_rfl (le_iSup _ a)
    _ = _ := by
      simp only [ENNReal.tsum_mul_right]
      congr 1
      rw [ENNReal.tsum_prod']

open scoped Classical in
/-- With the initial triangle trivial, remove the terminal trivial triangle
before splitting the weight. Its two costs are the nontrivial triangle mass
and the actual deleted mass at the diagonal input pair. -/
theorem first_diagram_nontrivial_terminal_weight_le [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (ψ : AddChar G Circle) :
    let w : G → ℝ≥0∞ := fun z => ENNReal.ofReal (1 - (ψ z : ℂ).re)
    let Γ := ∑' p : G × G, if p = (0, 0) then 0 else
      tau q 0 p.1 * tau q p.1 p.2 * tau q p.2 0
    let Md0 := ∑' s : G × G, diagramConnector q (0, 0) s * tau q s.1 s.2
    (∑' y, ∑' s : G × G, w y * (if s = (y, y) then 0 else
      diagramConnector q (0, 0) s * diagramReverseIterate q y 0 s)) ≤
      2 * (Γ + Md0) * ⨆ a, diagramWeightedPair q w a := by
  classical
  dsimp only
  let w : G → ℝ≥0∞ := fun z => ENNReal.ofReal (1 - (ψ z : ℂ).re)
  let Γ := ∑' p : G × G, if p = (0, 0) then 0 else
    tau q 0 p.1 * tau q p.1 p.2 * tau q p.2 0
  let Md0 := ∑' s : G × G, diagramConnector q (0, 0) s * tau q s.1 s.2
  let W := ⨆ a, diagramWeightedPair q w a
  have hw : w 0 = 0 := by simp [w]
  have hC := first_diagram_nontrivial_terminal_connector_mark_le q hq w
  have hT : (∑' y, ∑' s : G × G, (if s = (y, y) then 0 else
      diagramConnector q (0, 0) s * diagramReverseIterate q y 0 s) * w (y - s.2)) ≤
      Md0 * W := by
    calc
      _ ≤ ∑' y, ∑' s, diagramConnector q (0, 0) s *
          diagramReverseIterate q y 0 s * w (y - s.2) :=
        ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun s =>
          mul_le_mul' (by split_ifs <;> first | exact zero_le | exact le_rfl) le_rfl
      _ = diagramMarkedTerminalCore q w true (0, 0) := by
        rw [ENNReal.tsum_comm]
        unfold diagramMarkedTerminalCore
        apply tsum_congr
        intro s
        apply tsum_congr
        intro y
        simp only [diagramReverseIterate_zero, ite_true]
        ac_rfl
      _ ≤ _ := diagramMarkedTerminalCore_le_deleted_mass q hq w hw true (0, 0)
  have hroute (y t : G) : w y ≤ 2 * (w t + w (y - t)) := by
    have h := character_weight_add_le ψ t (y - t)
    have he : t + (y - t) = y := by abel
    simpa only [w, he] using h
  calc
    _ ≤ ∑' y, ∑' s : G × G, (2 * (w s.2 + w (y - s.2))) *
        (if s = (y, y) then 0 else
          diagramConnector q (0, 0) s * diagramReverseIterate q y 0 s) :=
      ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun s =>
        mul_le_mul' (hroute y s.2) le_rfl
    _ = 2 * ((∑' y, ∑' s : G × G, (if s = (y, y) then 0 else
          diagramConnector q (0, 0) s * diagramReverseIterate q y 0 s) * w s.2) +
        (∑' y, ∑' s : G × G, (if s = (y, y) then 0 else
          diagramConnector q (0, 0) s * diagramReverseIterate q y 0 s) * w (y - s.2))) := by
      simp_rw [← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro y
      apply tsum_congr
      intro s
      ring
    _ ≤ 2 * (Γ * W + Md0 * W) := mul_le_mul' le_rfl (add_le_add hC hT)
    _ = _ := by change _ = 2 * (Γ + Md0) * W; ring

open scoped Classical in
/-- The first diagram splits into the fully collapsed contribution, the
nontrivial initial piece, and the trivial-initial/nontrivial-terminal piece. -/
theorem first_diagram_weight_eq_diagonal_add_nontrivial
    (q : Sym2 G → unitInterval) (w : G → ℝ≥0∞) :
    (∑' y, w y * laceDiagram q 0 0 y) =
      (∑' y, w y * diagramConnector q (0, 0) (y, y)) +
      (∑' y, ∑' p : G × G, ∑' s, w y *
        ((if p.2 = 0 then 0 else diagramInitial q 0 p) * diagramConnector q p s *
          diagramReverseIterate q y 0 s)) +
      (∑' y, ∑' s : G × G, w y * (if s = (y, y) then 0 else
        diagramConnector q (0, 0) s * diagramReverseIterate q y 0 s)) := by
  classical
  have hD (y : G) : laceDiagram q 0 0 y =
      diagramConnector q (0, 0) (y, y) +
      (∑' p : G × G, ∑' s,
        (if p.2 = 0 then 0 else diagramInitial q 0 p) * diagramConnector q p s *
          diagramReverseIterate q y 0 s) +
      ∑' s : G × G, if s = (y, y) then 0 else
        diagramConnector q (0, 0) s * diagramReverseIterate q y 0 s := by
    have hT : (∑' s, diagramConnector q (0, 0) s * diagramReverseIterate q y 0 s) =
        diagramConnector q (0, 0) (y, y) +
        ∑' s : G × G, if s = (y, y) then 0 else
          diagramConnector q (0, 0) s * diagramReverseIterate q y 0 s := by
      rw [ENNReal.tsum_eq_add_tsum_ite (y, y)]
      simp only [diagramReverseIterate_zero, tau_self, mul_one]
      congr 1
      apply tsum_congr
      intro s
      split_ifs <;> rfl
    calc
      _ = ∑' p, diagramInitial q 0 p *
          (∑' s, diagramConnector q p s * diagramReverseIterate q y 0 s) := by
        simp only [laceDiagram, diagramIterate, diagramTerminal, diagramReverseIterate_zero]
        apply tsum_congr
        intro p
        congr 1
        apply tsum_congr
        intro s
        ac_rfl
      _ = _ := by
        rw [tsum_diagramInitial_mul_eq_diagonal_add, hT]
        simp_rw [← ENNReal.tsum_mul_left]
        simp only [mul_assoc]
        ac_rfl
  simp_rw [hD, mul_add, ENNReal.tsum_add, ← ENNReal.tsum_mul_left]

open scoped Classical in
/-- The first coefficient keeps a single collapsed-diagram term and the
small nontrivial initial mass. The forward, reverse and rooted deleted masses
remain distinct; no transfer reversibility or finiteness is assumed. -/
theorem laceCoefficient_one_character_weight_mass_le_deleted [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (ψ : AddChar G Circle) (Md Mr : ℝ≥0∞)
    (hMd : ∀ p, (∑' s : G × G, diagramConnector q p s * tau q s.1 s.2) ≤ Md)
    (hMr : ∀ r, (∑' t : G × G, diagramConnector q t r * tau q t.1 t.2) ≤ Mr) :
    let w : G → ℝ≥0∞ := fun z => ENNReal.ofReal (1 - (ψ z : ℂ).re)
    let a := ∑' p : G × G, if p.2 = 0 then 0 else diagramInitial q 0 p
    let Δ := ∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0
    let Γ := ∑' p : G × G, if p = (0, 0) then 0 else
      tau q 0 p.1 * tau q p.1 p.2 * tau q p.2 0
    let Md0 := ∑' s : G × G, diagramConnector q (0, 0) s * tau q s.1 s.2
    (∑' y, w y * laceCoefficient q 1 0 y) ≤
      (∑' y, w y * diagramConnector q (0, 0) (y, y)) +
        (3 * (Δ * Mr + a * Δ + a * Md) + 2 * (Γ + Md0)) *
          ⨆ z, diagramWeightedPair q w z := by
  classical
  dsimp only
  let w : G → ℝ≥0∞ := fun z => ENNReal.ofReal (1 - (ψ z : ℂ).re)
  refine (ENNReal.tsum_le_tsum fun y =>
    mul_le_mul' le_rfl (laceCoefficient_succ_le_laceDiagram q 0 0 y)).trans ?_
  change (∑' y, w y * laceDiagram q 0 0 y) ≤ _
  rw [first_diagram_weight_eq_diagonal_add_nontrivial]
  refine (add_le_add
    (add_le_add le_rfl (first_diagram_nontrivial_initial_weight_le q hq ψ Md Mr hMd hMr))
    (first_diagram_nontrivial_terminal_weight_le q hq ψ)).trans_eq ?_
  ring

open scoped Classical in
/-- The refined first weighted coefficient bound has leading coefficient one
on `W(0)`. It retains the smaller exact initial mass and the quadratic deleted
mass term instead of replacing them by full triangle factors. -/
theorem laceCoefficient_one_character_weight_mass_le [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (ψ : AddChar G Circle) (Md Mr : ℝ≥0∞)
    (hMd : ∀ p, (∑' s : G × G, diagramConnector q p s * tau q s.1 s.2) ≤ Md)
    (hMr : ∀ r, (∑' t : G × G, diagramConnector q t r * tau q t.1 t.2) ≤ Mr) :
    let w : G → ℝ≥0∞ := fun z => ENNReal.ofReal (1 - (ψ z : ℂ).re)
    let a := ∑' p : G × G, if p.2 = 0 then 0 else diagramInitial q 0 p
    let Δ := ∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0
    let Γ := ∑' p : G × G, if p = (0, 0) then 0 else
      tau q 0 p.1 * tau q p.1 p.2 * tau q p.2 0
    let Md0 := ∑' s : G × G, diagramConnector q (0, 0) s * tau q s.1 s.2
    (∑' y, w y * laceCoefficient q 1 0 y) ≤ diagramWeightedPair q w 0 +
      (3 * (Δ * Mr + a * Δ + a * Md) + 2 * (Γ + Md0)) *
        ⨆ z, diagramWeightedPair q w z := by
  dsimp only
  exact (laceCoefficient_one_character_weight_mass_le_deleted q hq ψ Md Mr hMd hMr).trans
    (add_le_add (tsum_weight_mul_diagonal_connector_le_weightedPair q _) le_rfl)

end PercLib.Percolation.Bond.Lace
