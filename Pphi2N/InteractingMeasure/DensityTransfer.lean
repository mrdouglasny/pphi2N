/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Density Transfer Bound (Cauchy-Schwarz)

For a probability measure μ with density ρ = (1/Z)exp(-V):

  ∫ F dμ_int ≤ K^{1/2} · (∫ F² dμ)^{1/2}

where K bounds ∫ exp(-2V) dμ (the Nelson estimate).

This is the key analytic tool connecting the interacting measure
to the free (Gaussian) measure. The proof is Cauchy-Schwarz:

  ∫ F·exp(-V) dμ ≤ (∫ F² dμ)^{1/2} · (∫ exp(-2V) dμ)^{1/2}

This is a GENERAL result — it works on any measurable space, not
just lattice fields. Both pphi2 and pphi2N use the same argument.

## Main results

- `density_transfer` — the bound for general measurable spaces
- `onInteracting_second_moment_bound` — applied to O(N) interaction

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. II
- Glimm-Jaffe, *Quantum Physics*, Ch. 6
-/

import Pphi2N.InteractingMeasure.ONTorusMeasure

noncomputable section

open GaussianField MeasureTheory BigOperators

namespace Pphi2N

/-! ## General density transfer bound -/

/-- **Cauchy-Schwarz density transfer.**

For a probability measure μ, a nonneg density ρ with ∫ ρ dμ = Z > 0,
and a nonneg measurable F with F² integrable:

  ∫ F dμ_ρ ≤ (1/Z) · (∫ F² dμ)^{1/2} · (∫ ρ² dμ)^{1/2}

where μ_ρ = (1/Z) · μ.withDensity ρ.

Proof: Cauchy-Schwarz applied to ∫ F·ρ dμ. -/
theorem density_transfer_general
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ρ : Ω → ℝ) (hρ_nn : ∀ ω, 0 ≤ ρ ω) (hρ_meas : Measurable ρ)
    (Z : ℝ) (hZ_pos : 0 < Z) (hZ_eq : ∫ ω, ρ ω ∂μ = Z)
    (F : Ω → ℝ) (hF_nn : ∀ ω, 0 ≤ F ω) (hF_meas : AEStronglyMeasurable F μ)
    (hF_sq_int : Integrable (fun ω => F ω ^ 2) μ)
    (K : ℝ) (hK_pos : 0 < K)
    (hK : ∫ ω, ρ ω ^ 2 ∂μ ≤ K) :
    ∫ ω, F ω ∂((ENNReal.ofReal Z)⁻¹ • μ.withDensity (fun ω => ENNReal.ofReal (ρ ω))) ≤
    (1 / Z) * K ^ (1/2 : ℝ) * (∫ ω, F ω ^ (2 : ℝ) ∂μ) ^ (1/2 : ℝ) := by
  sorry -- Cauchy-Schwarz: ∫ F·ρ ≤ ‖F‖₂ · ‖ρ‖₂, then divide by Z

/-! ## Application to O(N) interacting measure -/

variable (N : ℕ) (hN : 1 ≤ N) (d M : ℕ) [NeZero M]

/-- The second moment of the O(N) interacting measure is bounded by
the Gaussian fourth moment (hypercontractivity) times the Nelson bound.

  E_int[(ωf)²] ≤ (1/Z) · E_GFF[(ωf)⁴]^{1/2} · E_GFF[exp(-2V)]^{1/2}
              ≤ C · E_GFF[(ωf)²]²     (hypercontractivity)
              ≤ C · G(f,f)²            (Gaussian moment = Green's function)

For N components: each component contributes G(fᵢ,fᵢ), so
E_int[(ωf)²] ≤ C · (Σᵢ G(fᵢ,fᵢ))² ≤ C · N · Σᵢ G(fᵢ,fᵢ)²

The uniform bound follows from the uniform bound on G (from
gaussian-field's torusGreen_uniform_bound). -/
theorem onInteracting_second_moment_bound
    (P : ONInteraction) (c a : ℝ) (ha : 0 < a) (hc : 0 < c)
    (μ_scalar : Measure (FinLatticeField d M))
    [IsProbabilityMeasure μ_scalar]
    -- For any "observable" F : (Fin N → FinLatticeField d M) → ℝ that is
    -- nonneg, measurable, and has bounded Gaussian fourth moment:
    -- E_int[F] ≤ C · E_GFF[F²]^{1/2}
    (F : (Fin N → FinLatticeField d M) → ℝ)
    (hF_nn : ∀ φ, 0 ≤ F φ)
    (hF_meas : AEStronglyMeasurable F (nComponentMeasure N μ_scalar))
    (hF_sq_int : Integrable (fun φ => F φ ^ 2) (nComponentMeasure N μ_scalar))
    (K : ℝ) (hK_pos : 0 < K)
    (hK_nelson : ∫ φ, (onBoltzmannWeight N d M P c a φ) ^ 2
      ∂(nComponentMeasure N μ_scalar) ≤ K) :
    ∫ φ, F φ ∂(onInteractingMeasure N d M P c a μ_scalar) ≤
    (1 / onPartitionFunction N d M P c a μ_scalar) * K ^ (1/2 : ℝ) *
    (∫ φ, F φ ^ (2 : ℝ) ∂(nComponentMeasure N μ_scalar)) ^ (1/2 : ℝ) := by
  sorry -- Cauchy-Schwarz on ∫ F · exp(-V) dμ_GFF

end Pphi2N

end
