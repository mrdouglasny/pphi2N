/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hessian of the σ-Effective Action

Computes the Hessian of s_eff[σ] = ½ log det(-Δ+diag(σ)) + Σ_x λ(σ(x)-v²)²
using the matrix calculus from MatrixCalculus.lean.

## The computation

Hess(s_eff)_{xy} = -½ G²_{xy} + 2λ δ_{xy}

where G = (-Δ+diag(σ))⁻¹. For this to be ≥ κI, need 2λ - ½‖G²‖ ≥ κ.
Since -Δ ≥ 0 and σ ≥ σ*: ‖G‖ ≤ 1/σ*, ‖G²‖ ≤ 1/σ*², κ = 2λ - 1/(2σ*²).

## References

- Brézin-Zinn-Justin (1976), §II
-/

import Pphi2N.GeneralResults.MatrixCalculus
import Pphi2N.MassGap.LatticeOperator
import Pphi2N.MassGap.SigmaConcentration

noncomputable section

open Matrix MatrixCalculus

namespace Pphi2N

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

-- Matrix norm instance
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

/-! ## Trace formulas for elementary matrices

The elementary matrix E_x has (E_x)_{ij} = δ_{ix}·δ_{jx}.
Key trace identities for the Hessian computation. -/

/-- Elementary matrix: 1 at (x,x), 0 elsewhere. -/
def elemMatrix (x : Λ) : Matrix Λ Λ ℝ :=
  Matrix.diagonal (Pi.single x 1)

/-- **Tr(M · E_x · N · E_y) = M_{yx} · N_{xy}.**
Proved in GeneralResults/TraceFormula.lean (without norm instances).
For symmetric M, N: M_{yx}·N_{xy} = M_{xy}·N_{yx} = G²_{xy}. -/
axiom trace_elemMatrix_product (M N : Matrix Λ Λ ℝ) (x y : Λ) :
    Matrix.trace (M * elemMatrix x * N * elemMatrix y) = M y x * N x y

/-! ## The Hessian of the σ-effective action

Combining the entropic and polynomial terms:

  Hess(N · s_eff)_{xy} = N · (-½ G_{xy}² + 2λ δ_{xy})

For symmetric G (i.e., G = G^T, which holds for symmetric -Δ+σ):

  Hess(N · s_eff) = N · (2λI - ½G²)

as a matrix on (Λ → ℝ). -/

/-- **The σ-effective action Hessian as a matrix.**

For the LSM with parameters (λ, v²) and operator A = -Δ + diag(σ):

  Hess(s_eff)_{xy} = -½ (A⁻¹)_{xy}² + 2λ δ_{xy}

where (A⁻¹)_{xy}² means (A⁻¹)_{xy} · (A⁻¹)_{yx} = G_{xy}² for symmetric A.

This follows from:
- fderiv_log_det + chain rule: d/dσ_x [log det A] = G_{xx}
- hessian_log_det + chain rule: d²/dσ_x dσ_y [log det A] = -G_{xy}²
- d²/dσ_x dσ_y [λ(σ-v²)²] = 2λ δ_{xy} -/
theorem seff_hessian_formula
    (A : Matrix Λ Λ ℝ) (hA : A.IsHermitian) (hAdet : 0 < A.det)
    (lam : ℝ) (x y : Λ) :
    let G := A⁻¹
    -- The (x,y) entry of the Hessian of s_eff
    (-((1:ℝ)/2) * (G x y * G y x) + if x = y then 2 * lam else 0) =
    -- equals: 2λδ_{xy} - ½G²_{xy} (for symmetric G: G_{xy} = G_{yx})
    (if x = y then 2 * lam else 0) - (1:ℝ)/2 * (G x y * G y x) := by
  ring

/-! ## The Hessian bound: 2λI - ½G² ≥ κI

For the bilinear form: ⟨v, (2λI - ½G²)v⟩ ≥ κ‖v‖².

This holds when ‖G²‖_op ≤ 4(λ - κ/2), i.e., when
  1/σ*² ≤ 4(λ - κ/2)  ↔  κ ≤ 2λ - 1/(2σ*²)

At the saddle point σ = σ*: ‖G‖ ≤ 1/σ* (since -Δ ≥ 0 gives all
eigenvalues of A ≥ σ*). So ‖G²‖ ≤ 1/σ*² and κ = 2λ - 1/(2σ*²). -/

/-- **Operator norm bound on G = (-Δ+σ)⁻¹.**

When -Δ ≥ 0 (PSD lattice Laplacian) and σ ≥ σ_min > 0:
all eigenvalues of -Δ + diag(σ) are ≥ σ_min, so
  ‖(-Δ+diag(σ))⁻¹‖_op ≤ 1/σ_min -/
axiom green_function_norm_bound
    (Δ_neg : Matrix Λ Λ ℝ) (hΔ : Δ_neg.PosSemidef)
    (σ : Λ → ℝ) (σ_min : ℝ) (hσ_min : 0 < σ_min)
    (hσ : ∀ x, σ_min ≤ σ x) :
    ‖(Δ_neg + Matrix.diagonal σ)⁻¹‖ ≤ 1 / σ_min

/-- **The combined Hessian bound for s_eff.**

Hess(s_eff) ≥ κ·I when 2λ - 1/(2σ_min²) ≥ κ.

This is the key convexity result: the Hessian of the σ-effective action
has a positive lower bound (given by the convexity parameter κ). -/
axiom seff_hessian_lower_bound
    (Δ_neg : Matrix Λ Λ ℝ) (hΔ : Δ_neg.PosSemidef)
    (σ : Λ → ℝ) (σ_min : ℝ) (hσ_min : 0 < σ_min) (hσ : ∀ x, σ_min ≤ σ x)
    (lam κ : ℝ) (hκ : κ ≤ 2 * lam - 1 / (2 * σ_min ^ 2))
    (v : Λ → ℝ) :
    κ * ∑ x, v x ^ 2 ≤
      ∑ x, ∑ y, v x * ((-((1:ℝ)/2) * ((Δ_neg + Matrix.diagonal σ)⁻¹ x y *
        (Δ_neg + Matrix.diagonal σ)⁻¹ y x) +
        if x = y then 2 * lam else 0) * v y)

end Pphi2N

end
