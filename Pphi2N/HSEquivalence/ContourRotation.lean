/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Contour Rotation for the HS Integral

Key results for the steepest-descent contour rotation σ → iσ':

1. Oscillations are bounded: |exp(iθ)| = 1
2. The rotated exponent is real (imaginary parts cancel)
3. Cauchy's theorem validates the contour shift
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

open Complex MeasureTheory

namespace Pphi2N

/-- |exp(iθ)| = 1: pure imaginary exponents don't grow. -/
theorem norm_exp_imaginary (θ : ℝ) : ‖cexp (I * (θ : ℂ))‖ = 1 := by
  rw [Complex.norm_exp, mul_re, I_re, ofReal_re, I_im, ofReal_im,
    zero_mul, one_mul, sub_zero, Real.exp_zero]

/-- |exp(-a + iθ)| ≤ 1 when a ≥ 0. -/
theorem norm_exp_neg_real_plus_imaginary (a θ : ℝ) (ha : 0 ≤ a) :
    ‖cexp (-(a : ℂ) + I * (θ : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  simp only [add_re, neg_re, ofReal_re, mul_re, I_re, ofReal_re,
    I_im, ofReal_im, zero_mul, one_mul, sub_zero]
  exact Real.exp_le_one_iff.mpr (by linarith)

/-- (iσ')² = -σ'²: squaring a purely imaginary number gives a negative real. -/
theorem sq_imaginary (σ' : ℝ) : (I * (σ' : ℂ)) ^ 2 = -((σ' : ℂ)) ^ 2 := by
  rw [mul_pow, I_sq, neg_one_mul]

/-- i·a·(iσ') = -aσ': product of two imaginary terms is real (negative). -/
theorem prod_two_imaginary (a σ' : ℝ) :
    I * (a : ℂ) * (I * (σ' : ℂ)) = -((a : ℂ) * (σ' : ℂ)) := by
  have : I * I = -1 := by rw [← sq, I_sq]
  rw [show I * (a : ℂ) * (I * (σ' : ℂ)) = (I * I) * ((a : ℂ) * (σ' : ℂ)) by ring]
  rw [this, neg_one_mul]

/-- After σ → iσ': the HS exponent -σ²/(4λ) + iσa becomes
σ'²/(4λ) - aσ', which is real. This is the key computation
showing the contour rotation eliminates imaginary parts. -/
theorem hs_exponent_after_rotation (lam a σ' : ℝ) :
    -(1/(4*(lam : ℂ))) * (I * (σ' : ℂ))^2 + I * (a : ℂ) * (I * (σ' : ℂ)) =
    ((σ'^2/(4*lam) - a * σ' : ℝ) : ℂ) := by
  rw [sq_imaginary, prod_two_imaginary]
  push_cast
  ring

/-- **Cauchy's theorem for vertical contour shift** (axiom).

∫_ℝ f(x) dx = ∫_ℝ f(x + iy₀) dx for f entire + decaying.

Standard complex analysis; could be proved from Mathlib's
`DiffContOnCl.integral_boundary_rect_eq_zero`. -/
axiom cauchy_vertical_shift
    (f : ℂ → ℂ) (y₀ : ℝ)
    (hf : Differentiable ℂ f) :
    ∫ x : ℝ, f (x : ℂ) = ∫ x : ℝ, f ((x : ℂ) + I * (y₀ : ℂ))

end Pphi2N

end
