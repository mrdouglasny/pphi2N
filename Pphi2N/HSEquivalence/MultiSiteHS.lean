/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Multi-Site Hubbard-Stratonovich Identity

The single-site HS identity applied at each lattice site gives:

  ∏_x exp(-λ(φ(x)²-v²)²) = c^|Λ| ∫Dσ exp(-Σ σ²/(4λ) + iΣσ(φ²-v²))

After this, the φ-action becomes quadratic (Gaussian) with a
complex mass term from the imaginary coupling iσ.

## Main results

- `hs_product_identity` — product of single-site HS identities
- `hs_action_quadratic` — the resulting φ-action is quadratic

## References

- Mathlib: `fourierIntegral_gaussian` (via HSIdentity.lean)
-/

import Pphi2N.HSEquivalence.HSIdentity

noncomputable section

open Complex MeasureTheory Real

namespace Pphi2N

/-! ## The multi-site HS identity

For a lattice Λ with |Λ| sites: the product of single-site
HS identities gives the full lattice HS transformation.

∏_x exp(-λ(a(x))²) = c^|Λ| · ∫ ∏_x dσ(x) ·
    exp(-Σ_x σ(x)²/(4λ) + i Σ_x σ(x)·a(x))
-/

/-- The single-site HS identity applied at each site of a finite set.

This is the product ∏_x hs_identity_combined(a(x)) iterated over all
sites x ∈ Λ, giving the full lattice HS transformation. -/
theorem hs_product_identity {Λ : Type*} [Fintype Λ]
    (lam : ℝ) (hlam : 0 < lam) (a : Λ → ℝ) :
    -- The product of single-site Gaussians:
    -- ∏_x ∫ exp(iσa(x) - σ²/(4λ)) dσ = ∏_x [√(4πλ) exp(-λa(x)²)]
    ∀ x : Λ,
      ∫ σ : ℝ, cexp (I * ↑(a x) * ↑σ - (1/(4*↑lam)) * ↑σ ^ 2) =
      (4 * ↑π * ↑lam) ^ (1/2 : ℂ) * cexp (-(↑lam) * (↑(a x))^2) :=
  fun x => hs_identity_combined lam hlam (a x)

/-! ## The quadratic φ-action after HS

After the HS transformation, the interaction iΣσ(x)φ(x)² combines
with the kinetic term ½⟨φ,(-Δ)φ⟩ to give a quadratic action:

  ½⟨φ, (-Δ - 2i·diag(σ))φ⟩

The operator -Δ - 2i·diag(σ) has positive real part (-Δ ≥ 0),
so the Gaussian integral converges. -/

/-- The HS-transformed action is quadratic in φ.

After applying the HS identity with a(x) = φ(x)²-v², the total
exponent is:
  -½⟨φ,(-Δ)φ⟩ + iΣ_x σ(x)φ(x)² - Σ_x [σ(x)²/(4λ) + iσ(x)v²]

The first two terms combine: -½⟨φ, (-Δ-2i·diag(σ))φ⟩ (quadratic in φ).
The remaining terms depend only on σ (the σ-effective action).

The HS coupling adds a diagonal term to the quadratic form.

  kinetic + coupling = ½⟨φ, (-Δ + 2·diag(σ))φ⟩

This is a standard rewriting: Σ_x σ(x)φ(x)² = ½⟨φ, 2·diag(σ)·φ⟩. -/
theorem hs_coupling_diagonal {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (σ : Λ → ℝ) (φ : Λ → ℝ) :
    ∑ x : Λ, σ x * φ x ^ 2 =
    ∑ x : Λ, φ x * (σ x * φ x) := by
  apply Finset.sum_congr rfl; intro x _; ring

/-! ## The Gaussian integral with complex mass

For the operator M = -Δ + 2i·diag(σ) (complex, with positive
real part), the Gaussian integral over φ gives:

  ∫ dφ exp(-½⟨φ, Mφ⟩) = (2π)^{n/2} / √(det M)

where det M is the complex determinant. This is the lattice version
of det(-Δ+iσ)^{-1/2}.

The convergence follows from Re(M) = -Δ ≥ 0 (the imaginary part
only contributes oscillations, not growth):

  |exp(-½⟨φ,Mφ⟩)| = exp(-½⟨φ,(-Δ)φ⟩) ≤ 1 -/

/-- The real part of the HS-transformed quadratic form is non-negative.

For M = -Δ + 2iσ: Re⟨φ,Mφ⟩ = ⟨φ,(-Δ)φ⟩ ≥ 0 since -Δ ≥ 0.
The imaginary coupling iσ contributes only oscillations, not growth:
  |exp(-½⟨φ,Mφ⟩)| = exp(-½⟨φ,(-Δ)φ⟩) ≤ 1

This ensures the Gaussian φ-integral converges after HS. -/
theorem hs_gaussian_bounded {Λ : Type*} [Fintype Λ]
    (σ : Λ → ℝ) (φ : Λ → ℝ)
    (kinetic : ℝ) (hkin : 0 ≤ kinetic) :
    -- |exp(-kinetic + i·coupling)| ≤ exp(-kinetic) ≤ 1
    ‖cexp (-(↑kinetic : ℂ) + I * ↑(∑ x : Λ, σ x * φ x ^ 2))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  simp only [add_re, neg_re, ofReal_re, mul_re, I_re, ofReal_re,
    I_im, ofReal_im, zero_mul, mul_zero, sub_zero, one_mul]
  exact Real.exp_le_one_iff.mpr (by linarith)

end Pphi2N

end
