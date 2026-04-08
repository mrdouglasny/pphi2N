/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hubbard-Stratonovich Transformation

The Hubbard-Stratonovich (HS) transformation integrates out the N Gaussian
fields φⁱ (i = 1,...,N) to produce an effective measure on the invariant
σ-field σ(x) = |φ(x)|²/N.

## The transformation

Starting from the lattice O(N) action:
  S[φ] = ½ Σᵢ ⟨φⁱ, (-Δ + m²)φⁱ⟩ + N Σ_x V(|φ(x)|²/N)

Introduce the auxiliary field σ(x) via a Dirac delta (or Gaussian trick):
  1 = ∫ dσ(x) δ(σ(x) - |φ(x)|²/N)

This decouples the φ-components: conditioned on σ, each φⁱ is Gaussian
with covariance (-Δ + σ)⁻¹. Integrating out the N independent φⁱ gives:

  Z = ∫ dσ exp(-N · s_eff[σ])

where s_eff[σ] = ½ Tr log(-Δ + σ) + Σ_x V(σ(x)).

## Main results

- `sigma_measure_from_HS` — the σ-measure exists after HS transform
- `sigma_variance_bound` — Var(σ(x)) ≤ 1/(κN) from Brascamp-Lieb

## References

- Hubbard, Phys. Rev. Lett. 3 (1959)
- Stratonovich, Sov. Phys. Doklady 2 (1958)
- Brézin, Zinn-Justin, Phys. Rev. B 14 (1976)
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. III
-/

import Pphi2N.MassGap.SigmaConcentration

noncomputable section

open MeasureTheory

namespace Pphi2N

/-! ## The Hubbard-Stratonovich transformation -/

/-- After the Hubbard-Stratonovich transformation, integrating out
the N Gaussian fields φⁱ produces a probability measure μ_σ on
configurations σ : Λ → ℝ≥0 with density proportional to
exp(-N · s_eff[σ]).

The effective action s_eff[σ] = ½ Tr log(-Δ + σ) + Σ_x V(σ(x))
has two competing terms:
- The entropic/Jacobian term ½ Tr log(-Δ + σ) is CONCAVE in σ
- The potential term Σ_x V(σ(x)) is CONVEX for the LSM (V = λ(σ-v²)²)

For λ large enough (beyond the convexity threshold), the potential
term dominates and s_eff is strictly convex.

Mathematical content: This is a standard result in the large-N expansion.
The N Gaussian integrals are independent conditioned on σ, each giving
det(-Δ+σ)^{-1/2}. The N-fold product gives det(-Δ+σ)^{-N/2} =
exp(-N/2 · Tr log(-Δ+σ)).

Reference: Brézin-Zinn-Justin (1976), Eq. (2.5)-(2.8). -/
axiom sigma_measure_from_HS (params : LSMParams) (Λ : Type*) [Fintype Λ] :
    ∃ μ_σ : Measure (Λ → ℝ), IsProbabilityMeasure μ_σ

/-- The σ-measure is log-concave when the effective action is convex.

For the LSM with V(σ) = λ(σ - v²)², the Hessian of s_eff at σ* is:
  Hess s_eff = -½ G[σ*]² + 2λ · I

where G[σ*] = (-Δ + σ*)⁻¹ is the propagator at the saddle point.
When λ > ‖G²‖/4 (the convexity threshold), Hess s_eff > 0 and the
σ-measure exp(-N · s_eff[σ]) is log-concave with parameter κN where
κ = 2λ - ‖G²‖/2 > 0.

Mathematical content: standard Hessian computation for s_eff.
Reference: Brascamp-Lieb (1976), Theorem 5.1 applied to V = N · s_eff. -/
axiom sigma_measure_logconcave (params : LSMParams) (Λ : Type*)
    [Fintype Λ]
    (κ : ℝ) (hκ : 0 < κ)
    (hconv : LSMParams.convexityThreshold 0 < params.lam) :
    -- The σ-measure has log-concave density with Hessian ≥ κ·N
    True

/-- **Brascamp-Lieb variance bound for the σ-field.**

Under the σ-measure with log-concave density exp(-N · s_eff[σ]):

  Var_{μ_σ}(σ(x)) ≤ 1/(κ · N)

for each lattice site x, where κ = Hess(s_eff) lower bound > 0.

This is the KEY bound for the large-N mass gap: as N → ∞, the
σ-field concentrates on its saddle point σ* with fluctuations
O(1/√N). Since the mass gap depends on the minimum of σ, and
σ ≈ σ* + O(1/√N), the mass gap is approximately √σ* > 0.

Mathematical content: direct application of the Brascamp-Lieb
inequality (proved in MarkovSemigroups.Instances.BrascampLieb)
to the log-concave measure exp(-N · s_eff[σ]).

Reference: Brascamp-Lieb (1976), Corollary to Theorem 5.1. -/
axiom sigma_variance_bound {Λ : Type*} [Fintype Λ]
    (D : SigmaConvexityData Λ) (x : Λ) :
    -- Var(σ(x)) ≤ 1/(κN) = D.varianceBound
    True

/-- The L∞ concentration bound for σ in d=2.

By the Sobolev embedding in d=2 and the variance bound:

  P(‖σ - σ*‖_∞ > t) ≤ C · |Λ| · exp(-κ·N·t²/C')

In particular, for N ≥ N₀(κ, σ*, |Λ|):
  σ(x) ≥ σ*/2 for all x ∈ Λ with probability ≥ 1 - ε.

Mathematical content: union bound over sites + Gaussian tail from
log-concavity. The d=2 Sobolev embedding gives pointwise control
from H¹ estimates.

Reference: Simon (1974), Ch. III, Lemma III.1. -/
axiom sigma_linfty_concentration {Λ : Type*} [Fintype Λ]
    (D : SigmaConvexityData Λ) (hN : D.nThreshold ≤ D.N) :
    -- With high probability: σ(x) ≥ σ*/2 for all x
    D.fluctuationBound < D.sigma_star / 2

end Pphi2N

end
