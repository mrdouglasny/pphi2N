/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Mass Gap: Definitions

1. **Correlation decay**: |⟨φⁱ(x)φⁱ(0)⟩_c| ≤ C exp(-m|x|) with m > 0
2. **Transfer matrix spectral gap**: second eigenvalue < first

The mass gap PROOF will use HS with imaginary coupling + steepest
descent contour rotation + Brascamp-Lieb. See docs/mass-gap-v2.tex.

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

/-- **A system has a spectral gap.**

ev₀ > ev₁ ≥ 0 are the two largest eigenvalues of the transfer matrix,
giving mass gap m = log(ev₀/ev₁) > 0. -/
def HasSpectralGap (ev₀ ev₁ : ℝ) : Prop :=
  0 < ev₀ ∧ 0 ≤ ev₁ ∧ ev₁ < ev₀

/-! ## Mass gap theorem (target)

The mass gap for the O(N) LSM at large N will be proved via:
1. HS with imaginary coupling (exact at all N)
2. Steepest descent contour rotation (σ → iσ')
3. BL for the rotated (real, log-concave) measure
4. Renormalized Borell/FK bound with self-energy subtraction

See docs/mass-gap-v2.tex for the proof outline.
The N=1 case (P(φ)₂) serves as a test: see HSEquivalence/N1Test.lean. -/

end Pphi2N

end
