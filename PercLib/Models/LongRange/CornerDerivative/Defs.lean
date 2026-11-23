/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Models.LongRange.FluxRightLimit

/-!
# Definitions for the corner derivative-value bridge

These transparent definitions present the strict and closed radial selectors, the uncapped
weighted pivotal flux and the actual toReal `p`-th cutoff root moment on the full infinite lattice.
No capped cluster, finite-window model or replacement critical intensity occurs here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open PercLib.Percolation.Bond PercLib.Probability PercLib.Analysis
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

/-- The strict-ball radial selector at scale `r`: an edge of length `s` is kept when `s < r`. -/
def kernelSelStrict (r : ℝ) : ℝ → ℝ := fun s => if s < r then 1 else 0

/-- The closed-ball radial selector at scale `n`: an edge of length `s` is kept when `s ≤ n`. -/
def kernelSelClosed (n : ℝ) : ℝ → ℝ := fun s => if s ≤ n then 1 else 0

/-- The rate factor `β |K' r|` of the power-law profile at scale `r`. -/
def powerLawRate (d : ℕ) (α : ℝ) (β : ℝ≥0) (r : ℝ) : ℝ :=
  (β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1))

/-- The per-edge pivotal difference of the `p`-th cluster-moment observable at scale `r`. -/
def pivotalDefect (d : ℕ) (α : ℝ) (β : ℝ≥0) (p : ℕ) (r : ℝ)
    (e : Sym2 (Fin d → ℤ)) : ℝ :=
  ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
    ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
    ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) r) β))

/-- The per-edge weight of the pivotal flux at scale `r` with radial selector `sel`. -/
def pivotalWeight (d : ℕ) (α : ℝ) (β : ℝ≥0) (sel : ℝ → ℝ) (r : ℝ)
    (e : Sym2 (Fin d → ℤ)) : ℝ :=
  (radialKernel (normSeminorm ℝ (Fin d → ℝ)) sel e : ℝ) *
    (powerLawRate d α β r *
      Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ)))

/-- The whole weighted pivotal flux at scale `r` with radial selector `sel`. -/
def pivotalFlux (d : ℕ) (α : ℝ) (β : ℝ≥0) (p : ℕ) (sel : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∑' e : Sym2 (Fin d → ℤ), pivotalWeight d α β sel r e * pivotalDefect d α β p r e

/-- The pivotal flux with the **strict-ball** selector at its own scale (the derivative on a
corner-free window). -/
def fluxOpen (d : ℕ) (α : ℝ) (β : ℝ≥0) (p : ℕ) (r : ℝ) : ℝ :=
  pivotalFlux d α β p (kernelSelStrict r) r

/-- The pivotal flux with the **closed-ball** selector at scale `n` (the right limit at `n`). -/
def fluxClosedAt (d : ℕ) (α : ℝ) (β : ℝ≥0) (p : ℕ) (n : ℝ) : ℝ :=
  pivotalFlux d α β p (kernelSelClosed n) n

/-- The `toReal` real-valued `p`-th cut-off root moment at scale `r`. -/
def momToReal (d : ℕ) (α : ℝ) (β : ℝ≥0) (p : ℕ) (r : ℝ) : ℝ :=
  (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p
    ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) r) β))).toReal


end PercLib.Models.LongRange
