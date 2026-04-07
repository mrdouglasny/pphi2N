/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# N-Component Lattice GFF as Product Measure

The O(N) Gaussian free field on a finite lattice Λ is the product
of N independent scalar GFFs:

  μ_N = μ₁ ⊗ μ₁ ⊗ ... ⊗ μ₁  (N copies)

where μ₁ is the scalar lattice GFF with covariance G = (-Δ + m²)⁻¹.

## Construction

The N-component field φ = (φ¹,...,φᴺ) lives on the product space
`Fin N → Configuration E` where E is the scalar test function space.
The product measure is `Measure.pi (fun _ => μ₁)`.

## Covariance

⟨φⁱ(f) φʲ(g)⟩ = δⁱʲ · G(f, g)

where G(f,g) = ⟨Tf, Tg⟩ is the scalar Green's function.

## Main definitions

- `nComponentGFF` — the product GFF measure
- `nComponentGFF_isProbability` — product of prob measures is prob
- `nComponentGFF_covariance` — diagonal covariance δⁱʲ G(f,g)

## For interaction

The O(N)-invariant interaction couples the components through
|φ(x)|² = Σᵢ (φⁱ(x))². The interacting measure is defined by:

  μ_{int} = (1/Z) · exp(-V) · dμ_N

where V(φ) = Σ_x :P(|φ(x)|²):_c. This uses the generic
`interactingMeasure` from pphi2, applied to the product GFF as
base measure and the O(N) interaction as density.

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I
-/

import Pphi2N.LatticeField.NComponentField
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic

noncomputable section

open MeasureTheory BigOperators

namespace Pphi2N

/-! ## Product GFF

For any probability measure μ on a configuration space, the N-fold
product μ^⊗N lives on (Fin N → ConfigSpace). -/

variable {E : Type*} [MeasurableSpace E]

/-- The N-component GFF: product of N independent copies of a scalar
measure. Lives on `Fin N → E`. -/
def nComponentMeasure (N : ℕ) (μ : Measure E) :
    Measure (Fin N → E) :=
  Measure.pi (fun _ : Fin N => μ)

/-- The N-component GFF is a probability measure when the scalar one is. -/
instance nComponentMeasure_isProbability (N : ℕ) (μ : Measure E)
    [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (nComponentMeasure N μ) := by
  unfold nComponentMeasure; infer_instance

/-- Evaluation of the i-th component: the projection `(φ¹,...,φᴺ) ↦ φⁱ`
is measurable. -/
theorem nComponent_proj_measurable (N : ℕ) (i : Fin N) :
    Measurable (fun (φ : Fin N → E) => φ i) :=
  measurable_pi_apply i

/-! ## Covariance structure

The key property: the N-component GFF has diagonal covariance.
Components are independent:

  E_N[f(φⁱ) · g(φʲ)] = E₁[f(φ)] · E₁[g(φ)]  for i ≠ j
  E_N[f(φⁱ) · g(φⁱ)] = E₁[f(φ) · g(φ)]       for i = j

In particular:
  E_N[φⁱ(f) · φʲ(g)] = δⁱʲ · E₁[φ(f) · φ(g)] = δⁱʲ · G(f,g)
-/

/-- Independence of distinct components: for i ≠ j, the projections
to components i and j are independent under the product measure.

This is the defining property of the O(N) GFF and follows from
the product measure structure. -/
theorem nComponent_independent (N : ℕ) (μ : Measure E)
    [IsProbabilityMeasure μ]
    (i j : Fin N) (hij : i ≠ j)
    (f g : E → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ φ : Fin N → E, f (φ i) * g (φ j) ∂(nComponentMeasure N μ) =
    (∫ x, f x ∂μ) * (∫ x, g x ∂μ) := by
  sorry -- Independence of coordinate projections under Measure.pi
        -- via iIndepFun_pi + IndepFun.integral_mul_of_integrable

/-- Same-component expectation: for component i, the marginal is μ.

  E_N[f(φⁱ)] = E₁[f(φ)]  -/
theorem nComponent_marginal (N : ℕ) (μ : Measure E)
    [IsProbabilityMeasure μ]
    (i : Fin N) (f : E → ℝ) (hf : Integrable f μ) :
    ∫ φ : Fin N → E, f (φ i) ∂(nComponentMeasure N μ) =
    ∫ x, f x ∂μ := by
  -- The i-th projection from Measure.pi preserves the measure
  sorry -- measurePreserving_eval + integral_comp

end Pphi2N

end
