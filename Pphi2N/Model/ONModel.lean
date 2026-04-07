/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# O(N) Scalar Field Model

The O(N)-invariant P(φ)₂ model: N real scalar fields φ = (φ¹,...,φᴺ)
in 2D spacetime with interaction P(|φ|²) where P is a polynomial.

## Main definitions

- `ONModel` — bundles N, mass, interaction polynomial
- `ONModel.fieldDegree` — degree in the fields (= 2 × degree of P)
- `ONModel.pphi2` — the N=1 specialization (standard P(φ)₂)

## Key facts

- Target space: ℝ^N with standard inner product
- Internal symmetry: O(N) acting by rotation of field components
- Free theory: N independent copies of the scalar GFF
- Covariance: ⟨φⁱ(x) φʲ(y)⟩ = δⁱʲ G(x,y) where G = (-Δ + m²)⁻¹
- Wick constant: c_N(x) = N · G(x,x) (trace over N components)

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I, II
- Glimm-Jaffe, *Quantum Physics*, Ch. 6, 19
-/

import Pphi2N.Model.Interaction

noncomputable section

namespace Pphi2N

/-- The O(N) scalar field model in d=2 Euclidean spacetime.

Bundles the number of field components N, the mass m > 0, and the
O(N)-invariant interaction polynomial P(|φ|²).

For N=1 this reduces to the standard P(φ)₂ model. For N ≥ 2, the
interaction :P(|φ|²): is invariant under the continuous group O(N)
acting on the field components. -/
structure ONModel where
  /-- Number of field components. -/
  N : ℕ
  hN : 1 ≤ N
  /-- Mass parameter m > 0. -/
  mass : ℝ
  hmass : 0 < mass
  /-- The interaction polynomial P(t), acting on t = |φ|². -/
  interaction : ONInteraction

namespace ONModel

variable (M : ONModel)

/-- Degree in the fields (= 2 × degree of P in |φ|²). -/
def fieldDegree : ℕ := 2 * M.interaction.degree

/-- The field degree is ≥ 4 (quartic or higher). -/
theorem fieldDegree_ge : 4 ≤ M.fieldDegree := by
  unfold fieldDegree; have := M.interaction.hdeg; omega

/-- The standard P(φ)₂ model (N=1). -/
def pphi2 (P : ONInteraction) (mass : ℝ) (hmass : 0 < mass) : ONModel where
  N := 1
  hN := le_refl 1
  mass := mass
  hmass := hmass
  interaction := P

/-- The (|φ|⁴)₂ model at general N with quartic interaction. -/
def phi4 (N : ℕ) (hN : 1 ≤ N) (lam : ℝ) (hlam : 0 < lam)
    (mass : ℝ) (hmass : 0 < mass) : ONModel where
  N := N
  hN := hN
  mass := mass
  hmass := hmass
  interaction := quarticInteraction lam hlam

end ONModel

end Pphi2N

end
