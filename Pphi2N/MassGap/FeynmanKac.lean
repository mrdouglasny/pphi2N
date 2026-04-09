/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Feynman-Kac Mass Gap Axiom

The key axiom connecting the HS factorization + σ-concentration to
exponential decay of the φ-propagator.

## Statement

Given the O(N) LSM interacting measure μ on (Fin N → FinLatticeField d M):

1. The HS transformation gives an exact factorization:
   ⟨φⁱ(x)φⁱ(0)⟩_μ = E_σ[(-Δ+τ)⁻¹(x,0)]
   where (σ,φ) are jointly distributed with φ|σ Gaussian.

2. The σ-measure concentrates at σ* > 0 with BL cumulant bounds:
   Var(σ) ≤ 1/(κN), |κ_k| ≤ C^k k!/(κN)^{k-1}.

3. The Feynman-Kac representation:
   E_σ[(-Δ+τ)⁻¹(x,0)] = ∫₀^∞ ds E^W[exp(Σ κ_k(X)/k!)]
   where κ₁ = -sσ* gives mass √σ*, and higher κ_k give O(1/(κN))
   corrections in the exponent.

Conclusion: ⟨φⁱ(x)φⁱ(0)⟩_c decays exponentially with mass m > 0.

## References

- Glimm-Jaffe, *Quantum Physics*, Ch. 19
- Brascamp-Lieb (1976)
-/

import Pphi2N.MassGap.MassGapDef
import Pphi2N.InteractingMeasure.ONTorusMeasure

noncomputable section

open MeasureTheory GaussianField

namespace Pphi2N

/-! ## The Feynman-Kac mass gap axiom

This is the ONE axiom that bridges σ-concentration to φ-decay.
All other ingredients (HS, BL, Nelson, gap equation) are either
proved or standard.

The hypotheses encode: μ is an O(N) interacting measure whose
HS σ-field concentrates at σ* > 0 with convexity parameter κ.

The content: the Feynman-Kac path integral representation +
cumulant expansion shows the averaged propagator E_σ[(-Δ+σ)⁻¹(x,0)]
decays exponentially with mass m = √σ*(1 + O(1/(κN))). -/

/-- **The Feynman-Kac mass gap axiom.**

Given an O(N) interacting measure μ on the lattice, if:
- N ≥ 3 (excludes BKT for N=2)
- The HS σ-effective action has a saddle at σ* > 0
- The σ-Hessian is positive at σ* (convexity κ > 0, for BL)
- The lattice has a metric dist

Then the connected two-point function decays exponentially:
  |⟨φⁱ(x)φⁱ(0)⟩_c| ≤ C exp(-m dist(x,0)) with m > 0.

Mathematical content (to be formalized):
1. Feynman-Kac: G(x,0) = ∫₀^∞ ds E^W[E_σ[exp(-∫σ(ω)dt)]]
2. Cumulant expansion: E_σ[exp(·)] = exp(κ₁ + κ₂/2 + ...)
3. κ₁ = -sσ* gives tree-level mass √σ*
4. κ₂ = O(s/(κN)) from BL variance bound
5. Higher κ_k = O(s/(κN)^{k-1}) controlled in the exponent
6. Mass: m² = σ*(1 + O(1/(κN))) > 0 for N > C/κ -/
axiom feynmanKac_massGap
    -- Lattice parameters
    {d M : ℕ} [NeZero M]
    -- O(N) model parameters
    (N : ℕ) (hN : 3 ≤ N)
    -- σ-concentration data (from the gap equation + BL)
    (sigma_star : ℝ) (hsigma_star : 0 < sigma_star)
    (kappa : ℝ) (hkappa : 0 < kappa)
    -- Convexity condition: σ* large enough for BL at the saddle
    (hconvex : sigma_star > 1 / (16 * Real.pi * kappa))
    -- Lattice metric
    (dist : FinLatticeSites d M → FinLatticeSites d M → ℝ)
    -- The interacting measure
    (μ : Measure (Fin N → FinLatticeField d M))
    [IsProbabilityMeasure μ]
    -- Hypothesis: μ is an O(N) LSM measure whose HS σ-field
    -- concentrates at σ* with convexity κ
    -- (this connects μ to the σ-concentration data)
    (hμ_sigma_concentration :
      ∀ (x : FinLatticeSites d M),
        ∫ φ : Fin N → FinLatticeField d M,
          (∑ i : Fin N, (φ i x) ^ 2 / N - sigma_star) ^ 2 ∂μ
        ≤ 1 / (kappa * N)) :
    -- CONCLUSION: exponential decay of the two-point function
    HasCorrelationDecay μ dist

/-! ## The mass gap theorem -/

/-- **Mass gap for the O(N) LSM at large N.**

The connected two-point function decays exponentially, given
σ-concentration of the interacting measure. -/
theorem lsm_massGap
    {d M : ℕ} [NeZero M]
    (N : ℕ) (hN : 3 ≤ N)
    (sigma_star : ℝ) (hsigma_star : 0 < sigma_star)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hconvex : sigma_star > 1 / (16 * Real.pi * kappa))
    (dist : FinLatticeSites d M → FinLatticeSites d M → ℝ)
    (μ : Measure (Fin N → FinLatticeField d M))
    [IsProbabilityMeasure μ]
    (hμ : ∀ x, ∫ φ, (∑ i : Fin N, (φ i x) ^ 2 / N - sigma_star) ^ 2 ∂μ
      ≤ 1 / (kappa * N)) :
    HasCorrelationDecay μ dist :=
  feynmanKac_massGap N hN sigma_star hsigma_star kappa hkappa hconvex dist μ hμ

end Pphi2N

end
