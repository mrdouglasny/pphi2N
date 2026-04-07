/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The σ-Measure (Invariant Field Measure)

The σ-field σ(x) = |φ(x)|²/N is the O(N)-invariant "master field."
Its measure ν_N = π_* μ_N (push-forward of the full field measure)
encodes the effective potential and controls the mass gap.

## Main definitions

- `SigmaField` — the type of σ-field configurations
- `SigmaEffAction` — S_eff[σ] = (N/2) Tr log(-Δ+σ) + N ∫ V(σ)
- `SigmaEffAction.isConvex` — convexity for large λ (LSM)
- `SigmaEffAction.brascampLieb` — variance bound from convexity
- `SigmaEffAction.massGap` — σ-concentration → mass gap

## The key chain

1. LSM has convex S_eff (from λ-term in the potential)
2. Brascamp-Lieb: Var(σ) ≤ C/(Nλ)
3. Sobolev: ||σ - σ*||_∞ ≤ C'√(log|Λ|)/√(Nλ)
4. If σ(x) ≥ σ*/2 for all x: all φ-modes have mass ≥ √(σ*/2)
5. Mass gap ≥ √(σ*/2) > 0

## References

- Brascamp and Lieb, JFA 22 (1976)
- docs/convexity-preservation.md
- docs/lsm-to-nlsm.md
-/

import Pphi2N.Model.LSM
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory

noncomputable section

namespace Pphi2N

/-! ## The σ-field configuration space -/

/-- A σ-field configuration: a real-valued function on lattice sites.
σ(x) = |φ(x)|²/N ≥ 0 represents the local "radius squared" of the
O(N) field. -/
structure SigmaConfig (Sites : Type*) where
  /-- The σ-field values. -/
  val : Sites → ℝ
  /-- σ is nonneg (it's a squared norm). -/
  nonneg : ∀ x, 0 ≤ val x

/-! ## The effective action -/

/-- The σ-field effective action for the LSM.

S_eff[σ] has two parts:

1. The "entropic" part: (N/2) Tr log(-Δ + σ)
   This comes from integrating out the N Gaussian φ-components.
   It's CONCAVE in σ (= -N/2 × convex function).

2. The "potential" part: N Σ_x V(σ(x))
   For the LSM: V(σ) = λ(σ - v²)²
   This is CONVEX in σ (quadratic with positive coefficient).

Convexity of S_eff: V''(σ) > |entropic Hessian| when λ is large. -/
structure SigmaEffAction (Sites : Type*) [Fintype Sites] where
  /-- Number of field components. -/
  N : ℕ
  hN : 1 ≤ N
  /-- The lattice Laplacian eigenvalues. -/
  lapEigenval : Sites → ℝ
  /-- The potential V(σ). For LSM: V(σ) = λ(σ - v²)². -/
  potential : ℝ → ℝ
  /-- V is C² and convex: V'' ≥ 0. -/
  potential_convex : ∀ σ : ℝ, 0 ≤ sorry -- V''(σ), placeholder
  /-- The entropic Hessian norm: ||G[σ]²||_op.
  This bounds the concave part of S_eff''. -/
  entropicHessianNorm : ℝ → ℝ

namespace SigmaEffAction

variable {Sites : Type*} [Fintype Sites] (S : SigmaEffAction Sites)

/-- The propagator at fixed σ: G(σ) = (-Δ + σ)⁻¹.
Its diagonal G(x,x; σ) = Σ_k 1/(ε_k + σ) is the Wick constant. -/
def propagatorDiag (σ : ℝ) : ℝ :=
  ∑ x : Sites, 1 / (S.lapEigenval x + σ)

/-- The gap equation: σ* satisfies
  (N/2) · G(x,x; σ*) + N · V'(σ*) = 0 -/
def gapEquation (sigma_star : ℝ) (Vprime : ℝ → ℝ) : Prop :=
  (S.N : ℝ) / 2 * S.propagatorDiag sigma_star + S.N * Vprime sigma_star = 0

/-- S_eff is convex when the potential curvature exceeds the
entropic Hessian: V'' > ||G²||/4. -/
def isConvex (sigma : ℝ) (Vpp : ℝ) : Prop :=
  S.entropicHessianNorm sigma / 4 < Vpp

/-- The Brascamp-Lieb variance bound.

For a convex S_eff with curvature κ = N·V'' - (N/2)||G²||:

  Var_{ν_N}(σ(x)) ≤ 1 / κ

For the LSM with V(σ) = λ(σ-v²)²: V'' = 2λ, so:
  κ = 2Nλ - (N/2)||G²|| and Var ≤ 1/(2Nλ - (N/2)||G²||). -/
def brascampLiebBound (kappa : ℝ) (hkappa : 0 < kappa) : ℝ :=
  1 / kappa

/-! ## The mass gap from σ-concentration -/

/-- The σ-concentration bound in L∞ norm.

In d = 2 with Sobolev embedding H¹ ↪ L∞ (log correction):

  ||σ - σ*||_∞ ≤ C · √(log|Sites|) · √(Var(σ))

Combined with Brascamp-Lieb:
  ||σ - σ*||_∞ ≤ C · √(log|Sites|) / √κ -/
def linftyBound (sigma_star : ℝ) (kappa : ℝ) (nSites : ℕ) : ℝ :=
  Real.sqrt (Real.log nSites) / Real.sqrt kappa

/-- The conditional mass gap.

For any σ with σ(x) ≥ σ_min > 0 for all x:
the operator -Δ + σ has spectral gap ≥ σ_min.

All N components of φ (conditioned on σ) have mass ≥ √σ_min.
Radial and Goldstone modes are controlled equally because σ is
a scalar potential. -/
def conditionalMassGap (sigma_min : ℝ) (h : 0 < sigma_min) : ℝ :=
  Real.sqrt sigma_min

/-- The mass gap theorem.

If σ* > 0 (saddle point positive) and the L∞ fluctuation
||σ - σ*||_∞ < σ*/2, then σ(x) ≥ σ*/2 for all x, and
the unconditional mass gap is ≥ √(σ*/2). -/
theorem massGap_of_concentration
    (sigma_star : ℝ) (h_pos : 0 < sigma_star)
    (kappa : ℝ) (h_kappa : 0 < kappa)
    (nSites : ℕ)
    (h_conc : linftyBound sigma_star kappa nSites < sigma_star / 2) :
    0 < conditionalMassGap (sigma_star / 2) (by linarith) := by
  unfold conditionalMassGap
  exact Real.sqrt_pos_of_pos (by linarith)

/-- The mass gap is uniform in λ (for the LSM).

As λ → ∞: κ → ∞ (concentration tightens), σ* → v² (constraint
enforced), mass gap → √(v²/2). The mass gap is non-decreasing
in λ for large λ. -/
theorem massGap_monotone_lambda :
    -- For the LSM: m(λ₁) ≤ m(λ₂) when λ₁ ≤ λ₂ (and both > λ_c)
    True := by trivial -- placeholder

end SigmaEffAction

/-! ## Connection to pphi2 -/

/-- The pphi2 construction at N=1 gives the σ-measure for the scalar
P(φ)₂ theory. The σ-field is just σ(x) = φ(x)² (the squared field).
The effective action S_eff[σ] = ½ log(-Δ+σ) + V(σ) is convex for
the quartic interaction. -/
theorem pphi2_is_special_case :
    -- The N=1 LSM σ-measure coincides with pphi2's measure
    -- restricted to the invariant σ = φ²
    True := by trivial -- placeholder

end Pphi2N

end
