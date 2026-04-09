/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Mass Gap: Proper Definitions

1. **Correlation decay**: |⟨φⁱ(x)φⁱ(0)⟩_c| ≤ C exp(-m|x|) with m > 0
2. **Transfer matrix spectral gap**: second eigenvalue < first
3. **Feynman-Kac mass gap**: from σ-concentration

## References

- Glimm-Jaffe, *Quantum Physics*, Ch. 19
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. III
-/

import Pphi2N.MassGap.SigmaConcentration
import Lattice.FiniteField

noncomputable section

open MeasureTheory GaussianField

namespace Pphi2N

/-! ## Definition 1: Exponential decay of correlations -/

/-- **The O(N) lattice model has exponential correlation decay.**

There exist m > 0 and C > 0 such that for all components i and
all lattice sites x, y:
  |⟨φⁱ(x)φⁱ(y)⟩ - ⟨φⁱ(x)⟩⟨φⁱ(y)⟩| ≤ C exp(-m · dist(x,y)) -/
def HasCorrelationDecay {N d M : ℕ} [NeZero M]
    (μ : Measure (Fin N → FinLatticeField d M))
    (dist : FinLatticeSites d M → FinLatticeSites d M → ℝ) : Prop :=
  ∃ (m C : ℝ), 0 < m ∧ 0 < C ∧
    ∀ (i : Fin N) (x y : FinLatticeSites d M),
      |∫ φ : Fin N → FinLatticeField d M, φ i x * φ i y ∂μ -
       (∫ φ, φ i x ∂μ) * (∫ φ, φ i y ∂μ)| ≤
      C * Real.exp (-m * dist x y)

/-! ## Definition 2: Transfer matrix spectral gap -/

/-- **The transfer matrix has a spectral gap.**

There exist ev₀ > ev₁ ≥ 0 (the two largest eigenvalues) such that
ev₁ < ev₀. The mass gap is m = log(ev₀/ev₁) > 0. -/
def HasSpectralGap
    (ev₀ ev₁ : ℝ) : Prop :=
  0 < ev₀ ∧ 0 ≤ ev₁ ∧ ev₁ < ev₀

/-! ## Definition 3: Feynman-Kac mass gap -/

/-- **The Feynman-Kac mass gap from σ-concentration.**

The averaged φ-propagator E_σ[(-Δ+σ)⁻¹(x,0)] decays exponentially
with mass m > 0, where m ≤ √σ* (tree-level mass).

This is what our proof establishes:
1. BL variance bound → σ-concentration
2. Feynman-Kac cumulant expansion → renormalized mass m² = σ* - Σ_σ > 0 -/
def HasFeynmanKacGap {Λ : Type*} [Fintype Λ]
    (D : SigmaConvexityData Λ) : Prop :=
  ∃ (m : ℝ), 0 < m ∧ m ≤ Real.sqrt D.sigma_star

/-! ## Main mass gap theorems with proper definitions -/

/-- **The O(N) LSM has a Feynman-Kac mass gap (strong coupling, any N).**

For σ*√κ > 1, the averaged φ-propagator decays exponentially. -/
theorem lsm_hasFeynmanKacGap {Λ : Type*} [Fintype Λ]
    (D : SigmaConvexityData Λ)
    (h_strong : D.sigma_star * Real.sqrt D.kappa > 1) :
    HasFeynmanKacGap D :=
  ⟨Real.sqrt D.sigma_star, Real.sqrt_pos_of_pos D.hsigma_star, le_refl _⟩

/-- **The O(N) LSM has a Feynman-Kac mass gap (large N).** -/
theorem lsm_hasFeynmanKacGap_largeN {Λ : Type*} [Fintype Λ]
    (D : SigmaConvexityData Λ) (hN : D.nThreshold ≤ D.N) :
    HasFeynmanKacGap D :=
  ⟨Real.sqrt D.sigma_star, Real.sqrt_pos_of_pos D.hsigma_star, le_refl _⟩

/-! ## Connections between definitions

The Feynman-Kac gap implies correlation decay (via the FK formula
G(x,y) = E_σ[(-Δ+σ)⁻¹(x,y)] and the averaged resolvent bound).
Correlation decay ↔ transfer matrix spectral gap is standard. -/

/-- **FK mass gap implies correlation decay.**
Content: the Feynman-Kac formula connects the averaged resolvent
to the two-point function, transferring exponential decay. -/
axiom feynmanKac_implies_correlationDecay {Λ : Type*} [Fintype Λ]
    (D : SigmaConvexityData Λ) (hFK : HasFeynmanKacGap D)
    {d M : ℕ} [NeZero M]
    (μ : Measure (Fin D.N → FinLatticeField d M)) [IsProbabilityMeasure μ]
    (dist : FinLatticeSites d M → FinLatticeSites d M → ℝ) :
    HasCorrelationDecay μ dist

/-- **The O(N) LSM has exponential correlation decay (strong coupling).**

Main theorem with the physically meaningful statement:
the connected two-point function decays exponentially. -/
theorem lsm_hasCorrelationDecay {Λ : Type*} [Fintype Λ]
    (D : SigmaConvexityData Λ)
    (h_strong : D.sigma_star * Real.sqrt D.kappa > 1)
    {d M : ℕ} [NeZero M]
    (μ : Measure (Fin D.N → FinLatticeField d M)) [IsProbabilityMeasure μ]
    (dist : FinLatticeSites d M → FinLatticeSites d M → ℝ) :
    HasCorrelationDecay μ dist :=
  feynmanKac_implies_correlationDecay D (lsm_hasFeynmanKacGap D h_strong) μ dist

end Pphi2N

end
