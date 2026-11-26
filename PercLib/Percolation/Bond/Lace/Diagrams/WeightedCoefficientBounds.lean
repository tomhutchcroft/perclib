/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original finite-chain contractions for the actual lace coefficient diagrams;
no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.WeightedSums
public import PercLib.Percolation.Bond.Lace.Diagrams.Chains.Defs

/-!
# Weighted bounds for the actual lace coefficients

## Main results

Finite-chain identities identify a single marked connector or joining factor
with its forward/backward cut. Summing these identities connects the primitive
character route to the actual marked cores, retaining its linear route length.
-/

@[expose] public section
noncomputable section

open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

private theorem forward_eq_tsum_fin_chain {X : Type*}
    (A : X → ℝ≥0∞) (K : X → X → ℝ≥0∞) (F : ℕ → X → ℝ≥0∞)
    (h0 : ∀ p, F 0 p = A p)
    (hs : ∀ n p, F (n + 1) p = ∑' r, F n r * K r p) (n : ℕ) (p : X) :
    F n p = ∑' b : Fin n → X,
      A ((Fin.snoc b p : Fin (n + 1) → X) 0) *
        ∏ i : Fin n, K (b i) ((Fin.snoc b p : Fin (n + 1) → X) i.succ) := by
  classical
  induction n generalizing p with
  | zero =>
    simp only [h0, Fin.prod_univ_zero, mul_one]
    rw [tsum_eq_single (fun i : Fin 0 => Fin.elim0 i)
      (fun b hb => (hb (Subsingleton.elim _ _)).elim)]
    rfl
  | succ n ih =>
    rw [hs]
    simp_rw [ih, ← ENNReal.tsum_mul_right]
    symm
    rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => X)).tsum_eq,
      ENNReal.tsum_prod']
    apply tsum_congr
    intro r
    apply tsum_congr
    intro b
    change A ((Fin.snoc (Fin.snoc b r) p : Fin (n + 2) → X) 0) *
        (∏ i : Fin (n + 1), K ((Fin.snoc b r : Fin (n + 1) → X) i)
          ((Fin.snoc (Fin.snoc b r) p : Fin (n + 2) → X) i.succ)) =
      (A ((Fin.snoc b r : Fin (n + 1) → X) 0) *
        ∏ i : Fin n, K (b i) ((Fin.snoc b r : Fin (n + 1) → X) i.succ)) * K r p
    rw [Fin.snoc_apply_zero, Fin.prod_univ_castSucc]
    simp only [← Fin.castSucc_succ, Fin.snoc_castSucc, Fin.snoc_last, Fin.succ_last]
    ac_rfl

private theorem tsum_fin_chain_mark_last {X : Type*}
    (A : X → ℝ≥0∞) (K : X → X → ℝ≥0∞) (F : ℕ → X → ℝ≥0∞)
    (h0 : ∀ p, F 0 p = A p)
    (hs : ∀ n p, F (n + 1) p = ∑' r, F n r * K r p)
    (T f : X → ℝ≥0∞) (n : ℕ) :
    (∑' b : Fin (n + 1) → X,
      f (b (Fin.last n)) *
        (A (b 0) * (∏ i : Fin n, K (b i.castSucc) (b i.succ)) * T (b (Fin.last n)))) =
      ∑' p, F n p * f p * T p := by
  classical
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => X)).tsum_eq,
    ENNReal.tsum_prod']
  apply tsum_congr
  intro p
  rw [forward_eq_tsum_fin_chain A K F h0 hs]
  simp_rw [← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro b
  change f ((Fin.snoc b p : Fin (n + 1) → X) (Fin.last n)) *
    (A ((Fin.snoc b p : Fin (n + 1) → X) 0) *
      (∏ i : Fin n, K ((Fin.snoc b p : Fin (n + 1) → X) i.castSucc)
        ((Fin.snoc b p : Fin (n + 1) → X) i.succ)) *
          T ((Fin.snoc b p : Fin (n + 1) → X) (Fin.last n))) = _
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ac_rfl

private theorem tsum_fin_chain_node_mark {X : Type*}
    (A : X → ℝ≥0∞) (K : X → X → ℝ≥0∞) (F : ℕ → X → ℝ≥0∞)
    (h0 : ∀ p, F 0 p = A p)
    (hs : ∀ n p, F (n + 1) p = ∑' r, F n r * K r p)
    (T : X → ℝ≥0∞) (R : ℕ → X → ℝ≥0∞)
    (hR0 : ∀ p, R 0 p = T p)
    (hRs : ∀ n p, R (n + 1) p = ∑' r, K p r * R n r)
    (f : X → ℝ≥0∞) (n : ℕ) (i : Fin (n + 1)) :
    (∑' b : Fin (n + 1) → X,
      f (b i) * (A (b 0) * (∏ k : Fin n, K (b k.castSucc) (b k.succ)) *
        T (b (Fin.last n)))) =
      ∑' p, F i.val p * f p * R (n - i.val) p := by
  classical
  induction n generalizing T R with
  | zero =>
    have hi : i = Fin.last 0 := by ext; omega
    subst i
    simpa only [Fin.val_last, Nat.sub_self, hR0] using
      tsum_fin_chain_mark_last A K F h0 hs T f 0
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa only [Fin.val_last, Nat.sub_self, hR0] using
        tsum_fin_chain_mark_last A K F h0 hs T f (n + 1)
    · have htail :
          (∑' b : Fin (n + 2) → X,
            f (b i.castSucc) *
              (A (b 0) * (∏ k : Fin (n + 1), K (b k.castSucc) (b k.succ)) *
                T (b (Fin.last (n + 1))))) =
          ∑' b : Fin (n + 1) → X,
            f (b i) * (A (b 0) * (∏ k : Fin n, K (b k.castSucc) (b k.succ)) *
              (∑' p, K (b (Fin.last n)) p * T p)) := by
        rw [← (Fin.snocEquiv (fun _ : Fin (n + 2) => X)).tsum_eq,
          ENNReal.tsum_prod', ENNReal.tsum_comm]
        apply tsum_congr
        intro b
        simp_rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro p
        change f ((Fin.snoc b p : Fin (n + 2) → X) i.castSucc) *
          (A ((Fin.snoc b p : Fin (n + 2) → X) 0) *
            (∏ k : Fin (n + 1), K ((Fin.snoc b p : Fin (n + 2) → X) k.castSucc)
              ((Fin.snoc b p : Fin (n + 2) → X) k.succ)) *
                T ((Fin.snoc b p : Fin (n + 2) → X) (Fin.last (n + 1)))) = _
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_apply_zero, ← Fin.castSucc_succ,
          Fin.succ_last, Fin.snoc_last]
        ac_rfl
      rw [htail]
      have h := ih (fun p => ∑' r, K p r * T r) (fun j => R (j + 1))
        (fun p => by simpa only [hR0] using hRs 0 p)
        (fun j p => hRs (j + 1) p) i
      have hindex : n - i.val + 1 = n + 1 - i.val := by omega
      simpa only [Fin.val_castSucc, hindex] using h

private theorem tsum_fin_chain_edge_mark {X : Type*}
    (A : X → ℝ≥0∞) (K : X → X → ℝ≥0∞) (F : ℕ → X → ℝ≥0∞)
    (h0 : ∀ p, F 0 p = A p)
    (hs : ∀ n p, F (n + 1) p = ∑' r, F n r * K r p)
    (T : X → ℝ≥0∞) (R : ℕ → X → ℝ≥0∞)
    (hR0 : ∀ p, R 0 p = T p)
    (hRs : ∀ n p, R (n + 1) p = ∑' r, K p r * R n r)
    (f : X → X → ℝ≥0∞) (n : ℕ) (i : Fin n) :
    (∑' b : Fin (n + 1) → X,
      f (b i.castSucc) (b i.succ) *
        (A (b 0) * (∏ k : Fin n, K (b k.castSucc) (b k.succ)) * T (b (Fin.last n)))) =
      ∑' p, ∑' r, F i.val p * (K p r * f p r) * R (n - 1 - i.val) r := by
  classical
  induction n generalizing T R with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [← (Fin.snocEquiv (fun _ : Fin (n + 2) => X)).tsum_eq,
      ENNReal.tsum_prod']
    refine Fin.lastCases ?_ (fun i => ?_) i
    · change (∑' r, ∑' b : Fin (n + 1) → X,
        f ((Fin.snoc b r : Fin (n + 2) → X) (Fin.last n).castSucc)
          ((Fin.snoc b r : Fin (n + 2) → X) (Fin.last n).succ) *
            (A ((Fin.snoc b r : Fin (n + 2) → X) 0) *
              (∏ k : Fin (n + 1), K ((Fin.snoc b r : Fin (n + 2) → X) k.castSucc)
                ((Fin.snoc b r : Fin (n + 2) → X) k.succ)) *
                  T ((Fin.snoc b r : Fin (n + 2) → X) (Fin.last (n + 1))))) = _
      simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_apply_zero,
        ← Fin.castSucc_succ, Fin.succ_last, Fin.snoc_last, Fin.val_last,
        Nat.add_sub_cancel, Nat.sub_self, hR0]
      rw [ENNReal.tsum_comm]
      calc
        _ = ∑' r, ∑' b : Fin (n + 1) → X,
            (f (b (Fin.last n)) r * K (b (Fin.last n)) r) *
              (A (b 0) * (∏ k : Fin n, K (b k.castSucc) (b k.succ)) * T r) := by
          rw [ENNReal.tsum_comm]
          apply tsum_congr
          intro r
          apply tsum_congr
          intro b
          ac_rfl
        _ = ∑' r, ∑' p, F n p * (f p r * K p r) * T r := by
          apply tsum_congr
          intro r
          exact tsum_fin_chain_mark_last A K F h0 hs (fun _ => T r)
            (fun p => f p r * K p r) n
        _ = _ := by
          rw [ENNReal.tsum_comm]
          apply tsum_congr
          intro p
          apply tsum_congr
          intro r
          ac_rfl
    · have htail :
          (∑' r, ∑' b : Fin (n + 1) → X,
            f ((Fin.snoc b r : Fin (n + 2) → X) i.castSucc.castSucc)
              ((Fin.snoc b r : Fin (n + 2) → X) i.castSucc.succ) *
                (A ((Fin.snoc b r : Fin (n + 2) → X) 0) *
                  (∏ k : Fin (n + 1),
                    K ((Fin.snoc b r : Fin (n + 2) → X) k.castSucc)
                      ((Fin.snoc b r : Fin (n + 2) → X) k.succ)) *
                        T ((Fin.snoc b r : Fin (n + 2) → X) (Fin.last (n + 1))))) =
          ∑' b : Fin (n + 1) → X,
            f (b i.castSucc) (b i.succ) *
              (A (b 0) * (∏ k : Fin n, K (b k.castSucc) (b k.succ)) *
                (∑' r, K (b (Fin.last n)) r * T r)) := by
        rw [ENNReal.tsum_comm]
        apply tsum_congr
        intro b
        simp_rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro r
        rw [Fin.prod_univ_castSucc]
        simp only [← Fin.castSucc_succ, Fin.snoc_castSucc, Fin.snoc_apply_zero,
          Fin.succ_last, Fin.snoc_last]
        ac_rfl
      change (∑' r, ∑' b : Fin (n + 1) → X,
        f ((Fin.snoc b r : Fin (n + 2) → X) i.castSucc.castSucc)
          ((Fin.snoc b r : Fin (n + 2) → X) i.castSucc.succ) *
            (A ((Fin.snoc b r : Fin (n + 2) → X) 0) *
              (∏ k : Fin (n + 1), K ((Fin.snoc b r : Fin (n + 2) → X) k.castSucc)
                ((Fin.snoc b r : Fin (n + 2) → X) k.succ)) *
                  T ((Fin.snoc b r : Fin (n + 2) → X) (Fin.last (n + 1))))) = _
      rw [htail]
      have h := ih (fun p => ∑' r, K p r * T r) (fun j => R (j + 1))
        (fun p => by simpa only [hR0] using hRs 0 p)
        (fun j p => hRs (j + 1) p) i
      have hindex : n - 1 - i.val + 1 = n + 1 - 1 - i.val := by omega
      simpa only [Fin.val_castSucc, hindex] using h

variable {V : Type*}

private theorem primitive_weight_eq_state_chain
    (q : Sym2 V → unitInterval) (n : ℕ) (x y : V) (b s : Fin (n + 1) → V × V) :
    diagramPrimitiveChainWeight q n x y b s =
      (diagramInitial q x (b 0) * diagramConnector q (b 0) (s 0)) *
        (∏ i : Fin n, diagramInterior q (s i.castSucc) (b i.succ) *
          diagramConnector q (b i.succ) (s i.succ)) *
        (tau q (s (Fin.last n)).1 (s (Fin.last n)).2 *
          tau q (s (Fin.last n)).1 y * tau q (s (Fin.last n)).2 y) := by
  classical
  have hC : diagramConnector q (b 0) (s 0) *
      (∏ i : Fin n, diagramConnector q (b i.succ) (s i.succ)) =
      (∏ i : Fin n, diagramConnector q (b i.castSucc) (s i.castSucc)) *
        diagramConnector q (b (Fin.last n)) (s (Fin.last n)) := by
    rw [← Fin.prod_univ_succ (fun i => diagramConnector q (b i) (s i)),
      Fin.prod_univ_castSucc]
  simp only [diagramPrimitiveChainWeight, Finset.prod_mul_distrib]
  calc
    _ = diagramInitial q x (b 0) *
        ((∏ i : Fin n, diagramConnector q (b i.castSucc) (s i.castSucc)) *
          diagramConnector q (b (Fin.last n)) (s (Fin.last n))) *
        (∏ i : Fin n, diagramInterior q (s i.castSucc) (b i.succ)) *
        (tau q (s (Fin.last n)).1 (s (Fin.last n)).2 *
          tau q (s (Fin.last n)).1 y * tau q (s (Fin.last n)).2 y) := by ac_rfl
    _ = _ := by rw [← hC]; ac_rfl

private theorem tsum_primitive_mark_eq_state_chain
    (q : Sym2 V → unitInterval) (n : ℕ) (x y : V)
    (m : (Fin (n + 1) → V × V) → (Fin (n + 1) → V × V) → ℝ≥0∞) :
    (∑' b, ∑' s, m b s * diagramPrimitiveChainWeight q n x y b s) =
      ∑' z : Fin (n + 1) → (V × V) × (V × V),
        m (fun i => (z i).1) (fun i => (z i).2) *
        ((diagramInitial q x (z 0).1 * diagramConnector q (z 0).1 (z 0).2) *
          (∏ i : Fin n, diagramInterior q (z i.castSucc).2 (z i.succ).1 *
            diagramConnector q (z i.succ).1 (z i.succ).2) *
          (tau q (z (Fin.last n)).2.1 (z (Fin.last n)).2.2 *
            tau q (z (Fin.last n)).2.1 y * tau q (z (Fin.last n)).2.2 y)) := by
  classical
  rw [← ENNReal.tsum_prod' (f := fun bs :
    (Fin (n + 1) → V × V) × (Fin (n + 1) → V × V) =>
      m bs.1 bs.2 * diagramPrimitiveChainWeight q n x y bs.1 bs.2)]
  rw [← (Equiv.arrowProdEquivProdArrow (Fin (n + 1))
    (fun _ => V × V) (fun _ => V × V)).tsum_eq]
  apply tsum_congr
  intro z
  change m (fun i => (z i).1) (fun i => (z i).2) *
    diagramPrimitiveChainWeight q n x y (fun i => (z i).1) (fun i => (z i).2) = _
  rw [primitive_weight_eq_state_chain]

private theorem diagram_state_forward_succ (q : Sym2 V → unitInterval)
    (x : V) (n : ℕ) (p : (V × V) × (V × V)) :
    diagramIterate q x (n + 1) p.1 * diagramConnector q p.1 p.2 =
      ∑' r : (V × V) × (V × V),
        (diagramIterate q x n r.1 * diagramConnector q r.1 r.2) *
          (diagramInterior q r.2 p.1 * diagramConnector q p.1 p.2) := by
  simp only [diagramIterate, diagramTransfer, ENNReal.tsum_prod']
  simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro r
  apply tsum_congr
  intro s
  ac_rfl

private theorem diagram_state_reverse_succ (q : Sym2 V → unitInterval)
    (y : V) (n : ℕ) (p : (V × V) × (V × V)) :
    diagramReverseIterate q y (n + 1) p.2 =
      ∑' r : (V × V) × (V × V),
        (diagramInterior q p.2 r.1 * diagramConnector q r.1 r.2) *
          diagramReverseIterate q y n r.2 := by
  simp only [diagramReverseIterate_succ, ENNReal.tsum_prod']

/-- Summing all unmarked layers around one connector gives the exact
forward/backward cut. The mark may be any nonnegative function of its two states. -/
theorem tsum_primitive_chain_connector_mark_eq
    (q : Sym2 V → unitInterval) (x y : V) (n : ℕ) (i : Fin (n + 1))
    (f : (V × V) → (V × V) → ℝ≥0∞) :
    (∑' b, ∑' s, f (b i) (s i) * diagramPrimitiveChainWeight q n x y b s) =
      ∑' p, ∑' t, diagramIterate q x i.val p *
        (f p t * diagramConnector q p t) * diagramReverseIterate q y (n - i.val) t := by
  classical
  rw [tsum_primitive_mark_eq_state_chain]
  rw [tsum_fin_chain_node_mark
    (fun p : (V × V) × (V × V) =>
      diagramInitial q x p.1 * diagramConnector q p.1 p.2)
    (fun p r => diagramInterior q p.2 r.1 * diagramConnector q r.1 r.2)
    (fun k p => diagramIterate q x k p.1 * diagramConnector q p.1 p.2)
    (fun _ => rfl) (diagram_state_forward_succ q x)
    (fun p => tau q p.2.1 p.2.2 * tau q p.2.1 y * tau q p.2.2 y)
    (fun k p => diagramReverseIterate q y k p.2)
    (fun _ => rfl) (diagram_state_reverse_succ q y)
    (fun p => f p.1 p.2)]
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro p
  apply tsum_congr
  intro t
  ac_rfl

/-- A mark on an interior factor exposes both neighboring deleted connectors.
No symmetry of the deleted transfer is used in this exact contraction. -/
theorem tsum_primitive_chain_joining_mark_eq
    (q : Sym2 V → unitInterval) (x y : V) (n : ℕ) (i : Fin n)
    (f : (V × V) → (V × V) → ℝ≥0∞) :
    (∑' b, ∑' s, f (s i.castSucc) (b i.succ) *
      diagramPrimitiveChainWeight q n x y b s) =
      ∑' p, ∑' v, diagramIterate q x i.val p *
        (∑' s, ∑' t, diagramConnector q p s * diagramInterior q s t *
          diagramConnector q t v * f s t) *
            diagramReverseIterate q y (n - 1 - i.val) v := by
  classical
  rw [tsum_primitive_mark_eq_state_chain]
  rw [tsum_fin_chain_edge_mark
    (fun p : (V × V) × (V × V) =>
      diagramInitial q x p.1 * diagramConnector q p.1 p.2)
    (fun p r => diagramInterior q p.2 r.1 * diagramConnector q r.1 r.2)
    (fun k p => diagramIterate q x k p.1 * diagramConnector q p.1 p.2)
    (fun _ => rfl) (diagram_state_forward_succ q x)
    (fun p => tau q p.2.1 p.2.2 * tau q p.2.1 y * tau q p.2.2 y)
    (fun k p => diagramReverseIterate q y k p.2)
    (fun _ => rfl) (diagram_state_reverse_succ q y)
    (fun p r => f p.2 r.1)]
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro p
  simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  calc
    _ = ∑' s, ∑' t, ∑' v,
        (diagramIterate q x i.val p * diagramConnector q p s) *
          ((diagramInterior q s t * diagramConnector q t v) * f s t) *
            diagramReverseIterate q y (n - 1 - i.val) v := by
      apply tsum_congr
      intro s
      exact ENNReal.tsum_prod'
    _ = ∑' s, ∑' t, ∑' v, diagramIterate q x i.val p *
        (diagramConnector q p s * diagramInterior q s t * diagramConnector q t v * f s t) *
          diagramReverseIterate q y (n - 1 - i.val) v := by
      apply tsum_congr
      intro s
      apply tsum_congr
      intro t
      apply tsum_congr
      intro v
      ac_rfl
    _ = _ := by
      simpa only [ENNReal.tsum_prod'] using
        (ENNReal.tsum_comm (f := fun (st : (V × V) × (V × V)) v =>
          diagramIterate q x i.val p *
            (diagramConnector q p st.1 * diagramInterior q st.1 st.2 *
              diagramConnector q st.2 v * f st.1 st.2) *
                diagramReverseIterate q y (n - 1 - i.val) v))

variable {G : Type*} [AddCommGroup G]

/-- The entire primitive route is exactly the sum of the four kinds of
contracted marks. This is an identity of actual diagrams for arbitrary weights. -/
theorem tsum_primitive_route_mark_eq_sum_cores
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (n : ℕ) (x : G) :
    let c : Fin (n + 1) → (G × G) → G := fun i p => if Even i.val then p.2 else p.1
    (∑' y, ∑' b, ∑' s,
      (w (c 0 (b 0) - x) +
        (∑ i : Fin (n + 1), w (c i (s i) - c i (b i))) +
        (∑ i : Fin n, w (c i.succ (b i.succ) - c i.castSucc (s i.castSucc))) +
        w (y - c (Fin.last n) (s (Fin.last n)))) *
          diagramPrimitiveChainWeight q n x y b s) =
      (∑' r, diagramReverseIterate q 0 n r * diagramMarkedInitialCore q w x r) +
      (∑' p, diagramIterate q x n p *
        diagramMarkedTerminalCore q w (decide (Even n)) p) +
      (∑ i : Fin (n + 1), ∑' p, ∑' r,
        diagramIterate q x i.val p * diagramReverseIterate q 0 (n - i.val) r *
          diagramMarkedConnectorCore q w (decide (Even i.val)) p r) +
      (∑ i : Fin n, ∑' p, ∑' r,
        diagramIterate q x i.val p * diagramReverseIterate q 0 (n - 1 - i.val) r *
          diagramMarkedJoiningCore q w (decide (Even i.val)) p r) := by
  classical
  dsimp only
  have hI :
      (∑' y, ∑' b, ∑' s, w ((b 0).2 - x) *
        diagramPrimitiveChainWeight q n x y b s) =
        ∑' r, diagramReverseIterate q 0 n r * diagramMarkedInitialCore q w x r := by
    calc
      _ = ∑' y, ∑' p, ∑' s, diagramInitial q x p *
          (w (p.2 - x) * diagramConnector q p s) * diagramReverseIterate q y n s := by
        apply tsum_congr
        intro y
        simpa only [Fin.val_zero, Nat.sub_zero, diagramIterate] using
          tsum_primitive_chain_connector_mark_eq q x y n 0 (fun p _ => w (p.2 - x))
      _ = _ := markedInitial_mass_eq_tsum_core q hq w x n
  have hT :
      (∑' y, ∑' b, ∑' s, w (y -
        (if Even n then (s (Fin.last n)).2 else (s (Fin.last n)).1)) *
          diagramPrimitiveChainWeight q n x y b s) =
        ∑' p, diagramIterate q x n p *
          diagramMarkedTerminalCore q w (decide (Even n)) p := by
    rw [← markedTerminal_mass_eq_tsum_core q w (decide (Even n)) x n]
    apply tsum_congr
    intro y
    have h := tsum_primitive_chain_connector_mark_eq q x y n (Fin.last n)
      (fun _ t => w (y - (if Even n then t.2 else t.1)))
    simp only [Fin.val_last, Nat.sub_self, diagramReverseIterate_zero] at h
    refine h.trans ?_
    apply tsum_congr
    intro p
    apply tsum_congr
    intro s
    simp only [decide_eq_true_eq]
    ac_rfl
  have hC (i : Fin (n + 1)) :
      (∑' y, ∑' b, ∑' s,
        w ((if Even i.val then (s i).2 else (s i).1) -
          (if Even i.val then (b i).2 else (b i).1)) *
            diagramPrimitiveChainWeight q n x y b s) =
        ∑' p, ∑' r, diagramIterate q x i.val p *
          diagramReverseIterate q 0 (n - i.val) r *
            diagramMarkedConnectorCore q w (decide (Even i.val)) p r := by
    rw [← markedConnector_mass_eq_tsum_core_of_weight q hq w (decide (Even i.val))
      x i.val (n - i.val)]
    apply tsum_congr
    intro y
    simpa only [decide_eq_true_eq] using
      tsum_primitive_chain_connector_mark_eq q x y n i
        (fun p t => w ((if Even i.val then t.2 else t.1) -
          (if Even i.val then p.2 else p.1)))
  have hJ (i : Fin n) :
      (∑' y, ∑' b, ∑' s,
        w ((if Even i.succ.val then (b i.succ).2 else (b i.succ).1) -
          (if Even i.castSucc.val then (s i.castSucc).2 else (s i.castSucc).1)) *
            diagramPrimitiveChainWeight q n x y b s) =
        ∑' p, ∑' r, diagramIterate q x i.val p *
          diagramReverseIterate q 0 (n - 1 - i.val) r *
            diagramMarkedJoiningCore q w (decide (Even i.val)) p r := by
    have hpar (s t : G × G) :
        w ((if Even i.succ.val then t.2 else t.1) -
          (if Even i.castSucc.val then s.2 else s.1)) =
          w (if decide (Even i.val) then t.1 - s.2 else t.2 - s.1) := by
      by_cases hi : Even i.val <;> simp [Fin.val_succ, Nat.even_add_one, hi]
    simp_rw [hpar]
    rw [← markedJoining_mass_eq_tsum_core q hq w (decide (Even i.val))
      x i.val (n - 1 - i.val)]
    apply tsum_congr
    intro y
    exact tsum_primitive_chain_joining_mark_eq q x y n i
      (fun s t => w (if decide (Even i.val) then t.1 - s.2 else t.2 - s.1))
  simp only [Fin.val_zero, Even.zero, ↓reduceIte, Fin.val_last]
  simp_rw [add_mul, Finset.sum_mul, ENNReal.tsum_add,
    Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  rw [hI, hT]
  simp_rw [hC, hJ]
  ac_rfl

/-- An actual coefficient's character-weighted mass is bounded by the
proved local weighted-pair and second-geometry cores. The factor `2n+3` is
the length of its primitive route; alternating coordinates preserve the zero
joining marks and the distinct forward/backward powers. This estimate alone
does not assert a high-dimensional smallness bound for the core norms. -/
theorem laceCoefficient_succ_character_weight_mass_le [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (ψ : AddChar G Circle) (x : G) (n : ℕ) (ρ σ Md Mr : ℝ≥0∞)
    (hρ : ∀ p, (∑' r, diagramTransfer q p r) ≤ ρ)
    (hσ : ∀ p, (∑' s, ∑' r, diagramInterior q s r * diagramConnector q r p) ≤ σ)
    (hMd : ∀ p, (∑' s : G × G, diagramConnector q p s * tau q s.1 s.2) ≤ Md)
    (hMr : ∀ r, (∑' t : G × G, diagramConnector q t r * tau q t.1 t.2) ≤ Mr) :
    let w : G → ℝ≥0∞ := fun z => ENNReal.ofReal (1 - (ψ z : ℂ).re)
    let α := ∑' p, diagramInitial q x p
    let Δ := ∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0
    let W := ⨆ a, diagramWeightedPair q w a
    let J := ∑' v, offDiagonal (fun a b : G =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 v
    let H := ⨆ p, ⨆ r, diagramMarkedJoiningSecondCore q w p r
    (∑' y, w (y - x) * laceCoefficient q (n + 1) x y) ≤
      ((2 * n + 3 : ℕ) : ℝ≥0∞) *
        (Δ * σ ^ n * Mr * W + α * ρ ^ n * Md * W +
          (∑ i : Fin (n + 1), α * Δ * ρ ^ i.val * σ ^ (n - i.val) *
            ((if Even i.val then 1 else J) * W)) +
          (∑ i : Fin n, α * Δ * ρ ^ i.val * σ ^ (n - 1 - i.val) *
            (Md * Mr * W + if Even i.val then 0 else H))) := by
  classical
  dsimp only
  let w : G → ℝ≥0∞ := fun z => ENNReal.ofReal (1 - (ψ z : ℂ).re)
  have hw : w 0 = 0 := by simp [w]
  refine (ENNReal.tsum_le_tsum
    (fun y => laceCoefficient_succ_character_weight_le_primitive_chain q ψ n x y)).trans ?_
  rw [ENNReal.tsum_mul_left]
  change ((2 * n + 3 : ℕ) : ℝ≥0∞) *
    (∑' y, ∑' b, ∑' s,
      (w ((if Even (0 : Fin (n + 1)).val then (b 0).2 else (b 0).1) - x) +
        (∑ i : Fin (n + 1), w ((if Even i.val then (s i).2 else (s i).1) -
          (if Even i.val then (b i).2 else (b i).1))) +
        (∑ i : Fin n, w ((if Even i.succ.val then (b i.succ).2 else (b i.succ).1) -
          (if Even i.castSucc.val then (s i.castSucc).2 else (s i.castSucc).1))) +
        w (y - (if Even (Fin.last n).val then (s (Fin.last n)).2 else
          (s (Fin.last n)).1))) * diagramPrimitiveChainWeight q n x y b s) ≤ _
  rw [tsum_primitive_route_mark_eq_sum_cores q hq w n x]
  exact mul_le_mul' le_rfl (sum_marked_cuts_le q hq w hw x n ρ σ Md Mr hρ hσ hMd hMr)

end PercLib.Percolation.Bond.Lace
