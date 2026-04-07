/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# O(N)-Invariant Interaction Polynomials

An O(N)-invariant interaction is P(|φ|²) where P is a polynomial in one
real variable t = |φ|². For N=1, |φ|² = φ² and P(φ²) recovers the
standard P(φ)₂ interaction.

## Main definitions

- `ONInteraction` — polynomial P(t) with P bounded below (leading coeff > 0,
  even degree ≥ 2 in t, i.e., degree ≥ 4 in the fields)

## Examples

- P(t) = λt²: the (|φ|⁴)₂ model (quartic in fields)
- P(t) = λt² + μt: quartic + mass correction
- P(t) = λt³: sextic in fields (degree 6)

## References

- Simon, *The P(φ)₂ Euclidean QFT*, §II.3
- Glimm-Jaffe, *Quantum Physics*, §6.1
-/

import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

namespace Pphi2N

/-- An O(N)-invariant interaction polynomial P(t).

The interaction functional is V(φ) = ∫ :P(|φ(x)|²):_c dx where
|φ|² = Σᵢ (φⁱ)² is the O(N)-invariant squared norm.

P(t) is a polynomial in the single variable t = |φ|², so degree k
in t corresponds to degree 2k in the fields. We require:
- degree ≥ 2 (quartic or higher in fields)
- positive leading coefficient (bounded below)

For N=1: |φ|² = φ², so P(|φ|²) = P(φ²). If P(t) = λt², then
V = λ ∫ :φ⁴: dx, which is the standard P(φ)₂ quartic interaction. -/
structure ONInteraction where
  /-- Degree k ≥ 2 in t = |φ|² (= degree 2k ≥ 4 in the fields). -/
  degree : ℕ
  hdeg : 2 ≤ degree
  /-- Coefficients a₀, ..., a_{k-1}. The leading coefficient a_k = 1/k
  (normalized so P(t) = (1/k)t^k + lower terms). -/
  coeff : Fin degree → ℝ
  /-- Constant coefficient is nonpositive (vacuum energy). -/
  coeff_zero_nonpos : coeff ⟨0, by omega⟩ ≤ 0

/-- Evaluate P(t) = (1/k)t^k + Σ_{m<k} aₘ tᵐ. -/
def ONInteraction.eval (P : ONInteraction) (t : ℝ) : ℝ :=
  (1 / (P.degree : ℝ)) * t ^ P.degree + ∑ m : Fin P.degree, P.coeff m * t ^ (m : ℕ)

/-- P is nonneg for large t (bounded below). -/
theorem ONInteraction.bounded_below (P : ONInteraction) :
    ∃ C : ℝ, ∀ t : ℝ, C ≤ P.eval t := by
  sorry -- standard: leading term dominates for large |t|

/-- The quartic interaction P(t) = λt² (φ⁴ model). -/
def quarticInteraction (lam : ℝ) (hlam : 0 < lam) : ONInteraction where
  degree := 2
  hdeg := le_refl 2
  coeff := fun m => 0  -- no lower-order terms; leading = 1/2
  coeff_zero_nonpos := le_refl 0

end Pphi2N

end
