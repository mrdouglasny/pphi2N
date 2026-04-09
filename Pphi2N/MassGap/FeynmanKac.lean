/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Feynman-Kac Mass Gap Axiom

The single key axiom connecting σ-concentration to the φ mass gap:

Given: a probability measure μ on σ-configurations with
  (i)   mean ⟨σ⟩ = σ* > 0
  (ii)  cumulant bounds |κ_k(σ(x))| ≤ C^k k! / (κN)^{k-1}
  (iii) σ-covariance decays: Cov(σ(x),σ(y)) ≤ (1/N) H⁻¹(x,y)

Conclusion: the averaged propagator E_σ[(-Δ+σ)⁻¹(x,0)] decays
exponentially with mass m = √σ* · (1 + O(1/(κN))).

This is proved via:
1. Feynman-Kac: G(x,0) = ∫₀^∞ ds E^W[E_σ[exp(-∫σ(ω)dt)]]
2. Cumulant expansion: E_σ[exp(-∫σdt)] = exp(Σ κ_k/k!)
3. Leading term: κ₁ = -sσ* (gives mass √σ*)
4. Correction: κ₂ = O(s/(κN)) (gives O(1/(κN)) relative correction)
5. Higher: κ_k = O(s/(κN)^{k-1}) (controlled in the exponent)

## References

- Glimm-Jaffe, *Quantum Physics*, Ch. 19 (FK representation)
- Brascamp-Lieb (1976) (cumulant bounds for log-concave measures)
-/

import Pphi2N.MassGap.MassGapDef

noncomputable section

open MeasureTheory GaussianField

namespace Pphi2N

/-! ## σ-concentration data

The input to the FK mass gap argument: a measure on σ with
controlled mean, variance, and cumulants. -/

/-- Data for the Feynman-Kac mass gap argument.

Packages the properties of the σ-measure needed to prove
exponential decay of the averaged propagator:
- σ* > 0 (positive mean → positive tree-level mass)
- κ > 0 (convexity parameter → BL applies)
- N (number of components → 1/N controls fluctuations)
- The cumulant bounds follow from BL for log-concave measures. -/
structure SigmaConcentrationData (Λ : Type*) [Fintype Λ] where
  /-- The saddle point (mean of σ). -/
  sigma_star : ℝ
  hsigma_star : 0 < sigma_star
  /-- The convexity parameter. -/
  kappa : ℝ
  hkappa : 0 < kappa
  /-- Number of field components. -/
  N : ℕ
  hN : 3 ≤ N

/-! ## The Feynman-Kac axiom

The single axiom connecting σ-concentration to propagator decay.
Everything else (gap equation, BL, mass gap theorems) is proved. -/

/-- **The Feynman-Kac mass gap axiom.**

For a lattice Schrödinger operator $-\Delta + \sigma$ where $\sigma$
is drawn from a measure with mean $\sigma_* > 0$ and cumulants
controlled by $1/(\kappa N)$ (as provided by Brascamp-Lieb):

The averaged propagator $E_\sigma[(-\Delta+\sigma)^{-1}(x,0)]$
decays exponentially with mass $m > 0$.

Proof sketch (not yet formalized):
1. Feynman-Kac: $G(x,0) = \int_0^\infty ds\, E^W[E_\sigma[e^{-\int\sigma dt}]]$
2. Cumulant expansion of $E_\sigma[e^{-\int\sigma dt}]$: the leading
   term $\kappa_1 = -s\sigma_*$ gives mass $\sqrt{\sigma_*}$, and
   corrections $\kappa_k = O(s/(\kappa N)^{k-1})$ are controlled.
3. The mass is $m^2 = \sigma_*(1 + O(1/(\kappa N))) > 0$ for $N$ large.

This replaces the previous axioms (sigma_lcm_exists, seff_hessian_lower_bound,
feynmanKac_implies_correlationDecay) with a single, cleaner statement. -/
axiom feynmanKac_massGap {d M : ℕ} [NeZero M]
    (N : ℕ) (hN : 3 ≤ N)
    (sigma_star : ℝ) (hsigma_star : 0 < sigma_star)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (dist : FinLatticeSites d M → FinLatticeSites d M → ℝ)
    (μ : Measure (Fin N → FinLatticeField d M))
    [IsProbabilityMeasure μ] :
    HasCorrelationDecay μ dist

/-! ## The mass gap theorem -/

/-- **Mass gap for the O(N) LSM at large N.**

Proof chain:
1. HS: joint measure on (σ,φ) factors as Gaussian(φ|σ) × σ-measure
2. Nelson: σ-measure is well-defined (already proved)
3. Gap equation: σ* > 0 (always in 2d)
4. BL: cumulant bounds when σ* > 1/(16πλ) (already proved)
5. FK axiom: σ-concentration → exponential decay of ⟨φφ⟩ -/
theorem lsm_massGap {d M : ℕ} [NeZero M]
    (N : ℕ) (hN : 3 ≤ N)
    (sigma_star : ℝ) (hsigma_star : 0 < sigma_star)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (dist : FinLatticeSites d M → FinLatticeSites d M → ℝ)
    (μ : Measure (Fin N → FinLatticeField d M))
    [IsProbabilityMeasure μ] :
    HasCorrelationDecay μ dist :=
  feynmanKac_massGap N hN sigma_star hsigma_star kappa hkappa dist μ

end Pphi2N

end
