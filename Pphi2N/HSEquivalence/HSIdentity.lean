/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Hubbard-Stratonovich Identity

The Gaussian integral identity that underlies the HS transformation:

  exp(-λa²) = (1/√(4πλ)) ∫ exp(-σ²/(4λ) + iσa) dσ

This is the Fourier transform of the Gaussian, proved from
Mathlib's `fourierIntegral_gaussian`.

## References

- Mathlib: `fourierIntegral_gaussian`
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

noncomputable section

open Complex MeasureTheory Real

namespace Pphi2N

/-- **The HS identity (complex form).**

  ∫ exp(iax) · exp(-x²/(4λ)) dx = √(4πλ) · exp(-λa²)

This is `fourierIntegral_gaussian` from Mathlib with b = 1/(4λ). -/
theorem hs_identity_complex (lam : ℝ) (hlam : 0 < lam) (a : ℝ) :
    ∫ σ : ℝ, cexp (I * ↑a * ↑σ) * cexp (-(1/(4*↑lam)) * ↑σ ^ 2) =
    (↑π / (1/(4*↑lam))) ^ (1/2 : ℂ) * cexp (-(↑a)^2 / (4 * (1/(4*↑lam)))) := by
  have hb : (0 : ℝ) < ((1:ℂ)/(4*↑lam)).re := by
    rw [show (1:ℂ)/(4*↑lam) = ↑(1/(4*lam)) by push_cast; ring]
    simp only [ofReal_re]
    positivity
  exact fourierIntegral_gaussian hb (↑a)

/-- **The HS identity (combined exponential form).**

  ∫ exp(iaσ - σ²/(4λ)) dσ = √(4πλ) · exp(-λa²)

This combines the two exponentials and simplifies the prefactor. -/
theorem hs_identity_combined (lam : ℝ) (hlam : 0 < lam) (a : ℝ) :
    ∫ σ : ℝ, cexp (I * ↑a * ↑σ - (1/(4*↑lam)) * ↑σ ^ 2) =
    (4 * ↑π * ↑lam) ^ (1/2 : ℂ) * cexp (-(↑lam) * (↑a)^2) := by
  have h := hs_identity_complex lam hlam a
  -- Combine exponentials: exp(x)·exp(y) = exp(x+y)
  simp only [← Complex.exp_add] at h
  -- The LHS matches after rearranging
  have hLHS : ∀ σ : ℝ, I * ↑a * ↑σ + (-(1 / (4 * ↑lam)) * ↑σ ^ 2) =
      I * ↑a * ↑σ - (1 / (4 * ↑lam)) * ↑σ ^ 2 := fun σ => by ring
  simp_rw [hLHS] at h
  rw [h]
  -- Simplify the RHS
  congr 1
  · -- √(π/(1/(4λ))) = √(4πλ)
    congr 1
    have hlam' : (lam : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hlam)
    field_simp
  · -- exp(-a²/(4·(1/(4λ)))) = exp(-λa²)
    congr 1
    have hlam' : (lam : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hlam)
    field_simp

end Pphi2N

end
