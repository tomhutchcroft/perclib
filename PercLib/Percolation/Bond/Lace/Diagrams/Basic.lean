/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New definitions for this project; no upstream Lean code is copied.
The pair-state diagrams refine the construction of Heydenreich and van der
Hofstad (2017), Sections 7.3–7.5, by retaining outgoing bond deletion and
excluding the duplicated zero-length joining arm.
-/
module

public import PercLib.Percolation.Bond.Lace.Basic
public import PercLib.Percolation.Bond.WalkSum

/-!
# Deleted-bond pair-state diagrams

## Main results

The initial, connector, interior, transfer and terminal diagrams retain deletion and
the exact initial diagonal. Their iterates define the all-order coefficient bounds.
-/

@[expose] public section
noncomputable section

open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

open scoped Classical in
/-- Initial pair-state mass with the certain diagonal double connection
handled exactly. A state consists of the branch root and outgoing bond tail. -/
def diagramInitial (q : Sym2 V → unitInterval) (x : V) (p : V × V) : ℝ≥0∞ :=
  if p.2 = x then (if p.1 = x then 1 else 0)
  else tau q x p.1 * tau q x p.2 * tau q p.1 p.2

/-- Connector between consecutive layers, retaining the outgoing deleted
bond in the first layer. -/
def diagramConnector (q : Sym2 V → unitInterval) (p r : V × V) : ℝ≥0∞ :=
  ∑' v, offDiagonal (fun a b : V => (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) p.2 v *
    law q {ω : Config V | ω \ {s(p.2, v)} ∈ conn p.1 r.1} * tau q v r.2

open scoped Classical in
/-- Interior four-arm factor after extracting the incoming and outgoing
connections. The second geometry excludes the overlap already counted by the
first geometry. -/
def diagramInterior (q : Sym2 V → unitInterval) (p r : V × V) : ℝ≥0∞ :=
  tau q p.1 p.2 * tau q p.1 r.2 * tau q p.2 r.1 * tau q r.1 r.2 +
    if p.2 = r.1 then tau q p.1 r.2 *
      ∑' z, if z = r.1 then 0 else tau q r.1 z * tau q z p.1 * tau q z r.2
    else 0

/-- One complete interior step of the pair-state diagram. -/
def diagramTransfer (q : Sym2 V → unitInterval) (p r : V × V) : ℝ≥0∞ :=
  ∑' s, diagramConnector q p s * diagramInterior q s r

/-- Final step, keeping both arms to the target instead of replacing this
factor by another full interior transfer. -/
def diagramTerminal (q : Sym2 V → unitInterval) (p : V × V) (y : V) : ℝ≥0∞ :=
  ∑' s : V × V, diagramConnector q p s * tau q s.1 s.2 * tau q s.1 y * tau q s.2 y

/-- Initial diagram row after `n` interior transfers. -/
def diagramIterate (q : Sym2 V → unitInterval) (x : V) (n : ℕ) (p : V × V) : ℝ≥0∞ :=
  match n with
  | 0 => diagramInitial q x p
  | n + 1 => ∑' r, diagramIterate q x n r * diagramTransfer q r p

/-- The terminal triangle propagated backwards through the actual `B C_d`
product. The endpoint remains explicit; no reversal identity is used. -/
def diagramReverseIterate (q : Sym2 V → unitInterval) (y : V) (n : ℕ)
    (p : V × V) : ℝ≥0∞ :=
  match n with
  | 0 => tau q p.1 p.2 * tau q p.1 y * tau q p.2 y
  | n + 1 => ∑' r, ∑' t, diagramInterior q p r * diagramConnector q r t *
      diagramReverseIterate q y n t

@[simp] theorem diagramReverseIterate_zero (q : Sym2 V → unitInterval)
    (y : V) (p : V × V) :
    diagramReverseIterate q y 0 p = tau q p.1 p.2 * tau q p.1 y * tau q p.2 y := rfl

@[simp] theorem diagramReverseIterate_succ (q : Sym2 V → unitInterval)
    (y : V) (n : ℕ) (p : V × V) :
    diagramReverseIterate q y (n + 1) p =
      ∑' r, ∑' t, diagramInterior q p r * diagramConnector q r t *
        diagramReverseIterate q y n t := rfl

/-- The pair-state diagram bounding the coefficient of order `n+1`. -/
def laceDiagram (q : Sym2 V → unitInterval) (n : ℕ) (x y : V) : ℝ≥0∞ :=
  ∑' p, diagramIterate q x n p * diagramTerminal q p y

section Marked

variable {G : Type*} [AddGroup G]

/-- The actual connector core after summing a common translation of the
outgoing pair. `true` marks the second coordinate, `false` the first. -/
def diagramMarkedConnectorCore (q : Sym2 G → unitInterval) (w : G → ℝ≥0∞)
    (ε : Bool) (p r : G × G) : ℝ≥0∞ :=
  ∑' y, w ((if ε then r.2 else r.1) + y - (if ε then p.2 else p.1)) *
    diagramConnector q p (r.1 + y, r.2 + y)

/-- The shifted weighted pair. For the character weight this is `W(a;k)`;
its supremum is the local norm for a mark on the second connector coordinate. -/
def diagramWeightedPair (q : Sym2 G → unitInterval) (w : G → ℝ≥0∞) (a : G) : ℝ≥0∞ :=
  ∑' z, w z * (∑' v, offDiagonal (fun a b : G =>
    (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 v * tau q v z) * tau q 0 (z + a)

@[simp] theorem diagramMarkedConnectorCore_true (q : Sym2 G → unitInterval)
    (w : G → ℝ≥0∞) (p r : G × G) :
    diagramMarkedConnectorCore q w true p r =
      ∑' y, w (r.2 + y - p.2) * diagramConnector q p (r.1 + y, r.2 + y) := rfl

@[simp] theorem diagramMarkedConnectorCore_false (q : Sym2 G → unitInterval)
    (w : G → ℝ≥0∞) (p r : G × G) :
    diagramMarkedConnectorCore q w false p r =
      ∑' y, w (r.1 + y - p.1) * diagramConnector q p (r.1 + y, r.2 + y) := rfl

@[simp] theorem diagramMarkedConnectorCore_zero_weight (q : Sym2 G → unitInterval)
    (ε : Bool) (p r : G × G) :
    diagramMarkedConnectorCore q (fun _ => 0) ε p r = 0 := by
  simp [diagramMarkedConnectorCore]

theorem diagramMarkedConnectorCore_mono_weight (q : Sym2 G → unitInterval)
    {w w' : G → ℝ≥0∞} (hw : w ≤ w') (ε : Bool) (p r : G × G) :
    diagramMarkedConnectorCore q w ε p r ≤ diagramMarkedConnectorCore q w' ε p r :=
  ENNReal.tsum_le_tsum fun _ => mul_le_mul' (hw _) le_rfl

theorem diagramWeightedPair_eq_tsum (q : Sym2 G → unitInterval)
    (w : G → ℝ≥0∞) (a : G) :
    diagramWeightedPair q w a = ∑' z, w z * (∑' v, offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 v * tau q v z) * tau q 0 (z + a) := rfl

@[simp] theorem diagramWeightedPair_zero_weight (q : Sym2 G → unitInterval) (a : G) :
    diagramWeightedPair q (fun _ => 0) a = 0 := by
  simp [diagramWeightedPair]

theorem diagramWeightedPair_mono_weight (q : Sym2 G → unitInterval)
    {w w' : G → ℝ≥0∞} (hw : w ≤ w') (a : G) :
    diagramWeightedPair q w a ≤ diagramWeightedPair q w' a :=
  ENNReal.tsum_le_tsum fun z => mul_le_mul' (mul_le_mul' (hw z) le_rfl) le_rfl

/-- The actual joining core with both adjacent deleted connectors. `true`
marks incoming second to outgoing first; `false` marks first to second. -/
def diagramMarkedJoiningCore (q : Sym2 G → unitInterval) (w : G → ℝ≥0∞)
    (ε : Bool) (p r : G × G) : ℝ≥0∞ :=
  ∑' s, ∑' t, ∑' y, diagramConnector q p s * diagramInterior q s t *
    diagramConnector q t (r.1 + y, r.2 + y) *
      w (if ε then t.1 - s.2 else t.2 - s.1)

open scoped Classical in
/-- The second joining geometry with its actual excluded diagonal and both
deleted connectors. This is the local `H` diagram before any norm bound. -/
def diagramMarkedJoiningSecondCore (q : Sym2 G → unitInterval) (w : G → ℝ≥0∞)
    (p r : G × G) : ℝ≥0∞ :=
  ∑' u, ∑' v, ∑' t, ∑' y, diagramConnector q p (u, v) * tau q u t *
    (∑' z, if z = v then 0 else tau q v z * tau q z u * tau q z t) *
      diagramConnector q (v, t) (r.1 + y, r.2 + y) * w (t - u)

theorem diagramMarkedJoiningCore_eq_tsum (q : Sym2 G → unitInterval)
    (w : G → ℝ≥0∞) (ε : Bool) (p r : G × G) :
    diagramMarkedJoiningCore q w ε p r =
      ∑' s, ∑' t, ∑' y, diagramConnector q p s * diagramInterior q s t *
        diagramConnector q t (r.1 + y, r.2 + y) *
          w (if ε then t.1 - s.2 else t.2 - s.1) := rfl

open scoped Classical in
theorem diagramMarkedJoiningSecondCore_eq_tsum (q : Sym2 G → unitInterval)
    (w : G → ℝ≥0∞) (p r : G × G) :
    diagramMarkedJoiningSecondCore q w p r =
      ∑' u, ∑' v, ∑' t, ∑' y, diagramConnector q p (u, v) * tau q u t *
        (∑' z, if z = v then 0 else tau q v z * tau q z u * tau q z t) *
          diagramConnector q (v, t) (r.1 + y, r.2 + y) * w (t - u) := rfl

@[simp] theorem diagramMarkedJoiningCore_zero_weight (q : Sym2 G → unitInterval)
    (ε : Bool) (p r : G × G) :
    diagramMarkedJoiningCore q (fun _ => 0) ε p r = 0 := by
  simp [diagramMarkedJoiningCore]

@[simp] theorem diagramMarkedJoiningSecondCore_zero_weight (q : Sym2 G → unitInterval)
    (p r : G × G) : diagramMarkedJoiningSecondCore q (fun _ => 0) p r = 0 := by
  simp [diagramMarkedJoiningSecondCore]

theorem diagramMarkedJoiningCore_mono_weight (q : Sym2 G → unitInterval)
    {w w' : G → ℝ≥0∞} (hw : w ≤ w') (ε : Bool) (p r : G × G) :
    diagramMarkedJoiningCore q w ε p r ≤ diagramMarkedJoiningCore q w' ε p r :=
  ENNReal.tsum_le_tsum fun _ => ENNReal.tsum_le_tsum fun _ =>
    ENNReal.tsum_le_tsum fun _ => mul_le_mul' le_rfl (hw _)

theorem diagramMarkedJoiningSecondCore_mono_weight (q : Sym2 G → unitInterval)
    {w w' : G → ℝ≥0∞} (hw : w ≤ w') (p r : G × G) :
    diagramMarkedJoiningSecondCore q w p r ≤ diagramMarkedJoiningSecondCore q w' p r :=
  ENNReal.tsum_le_tsum fun _ => ENNReal.tsum_le_tsum fun _ =>
    ENNReal.tsum_le_tsum fun _ => ENNReal.tsum_le_tsum fun _ => mul_le_mul' le_rfl (hw _)

/-- The initial route mark is on the second coordinate. The outgoing pair
is translated together with the endpoint of the remaining chain. -/
def diagramMarkedInitialCore (q : Sym2 G → unitInterval) (w : G → ℝ≥0∞)
    (x : G) (r : G × G) : ℝ≥0∞ :=
  ∑' s, ∑' y, w (s.2 - x) * diagramInitial q x s *
    diagramConnector q s (r.1 + y, r.2 + y)

/-- The terminal route mark starts at the second coordinate when `true`,
and at the first coordinate when `false`. The deleted connector remains actual. -/
def diagramMarkedTerminalCore (q : Sym2 G → unitInterval) (w : G → ℝ≥0∞)
    (ε : Bool) (p : G × G) : ℝ≥0∞ :=
  ∑' s, ∑' y, diagramConnector q p s * tau q s.1 s.2 * tau q s.1 y * tau q s.2 y *
    w (y - (if ε then s.2 else s.1))

theorem diagramMarkedInitialCore_eq_tsum (q : Sym2 G → unitInterval)
    (w : G → ℝ≥0∞) (x : G) (r : G × G) :
    diagramMarkedInitialCore q w x r =
      ∑' s, ∑' y, w (s.2 - x) * diagramInitial q x s *
        diagramConnector q s (r.1 + y, r.2 + y) := rfl

theorem diagramMarkedTerminalCore_eq_tsum (q : Sym2 G → unitInterval)
    (w : G → ℝ≥0∞) (ε : Bool) (p : G × G) :
    diagramMarkedTerminalCore q w ε p =
      ∑' s, ∑' y, diagramConnector q p s * tau q s.1 s.2 * tau q s.1 y * tau q s.2 y *
        w (y - (if ε then s.2 else s.1)) := rfl

@[simp] theorem diagramMarkedInitialCore_zero_weight (q : Sym2 G → unitInterval)
    (x : G) (r : G × G) : diagramMarkedInitialCore q (fun _ => 0) x r = 0 := by
  simp [diagramMarkedInitialCore]

@[simp] theorem diagramMarkedTerminalCore_zero_weight (q : Sym2 G → unitInterval)
    (ε : Bool) (p : G × G) : diagramMarkedTerminalCore q (fun _ => 0) ε p = 0 := by
  simp [diagramMarkedTerminalCore]

theorem diagramMarkedInitialCore_mono_weight (q : Sym2 G → unitInterval)
    {w w' : G → ℝ≥0∞} (hw : w ≤ w') (x : G) (r : G × G) :
    diagramMarkedInitialCore q w x r ≤ diagramMarkedInitialCore q w' x r :=
  ENNReal.tsum_le_tsum fun _ => ENNReal.tsum_le_tsum fun _ =>
    mul_le_mul' (mul_le_mul' (hw _) le_rfl) le_rfl

theorem diagramMarkedTerminalCore_mono_weight (q : Sym2 G → unitInterval)
    {w w' : G → ℝ≥0∞} (hw : w ≤ w') (ε : Bool) (p : G × G) :
    diagramMarkedTerminalCore q w ε p ≤ diagramMarkedTerminalCore q w' ε p :=
  ENNReal.tsum_le_tsum fun _ => ENNReal.tsum_le_tsum fun _ => mul_le_mul' le_rfl (hw _)

end Marked

end PercLib.Percolation.Bond.Lace
