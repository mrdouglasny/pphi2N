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
import Mathlib.Probability.Independence.Integration

noncomputable section

open MeasureTheory BigOperators ProbabilityTheory

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

/-- Same-component expectation: for component i, the marginal is μ.

  E_N[f(φⁱ)] = E₁[f(φ)]  -/
theorem nComponent_marginal (N : ℕ) (μ : Measure E)
    [IsProbabilityMeasure μ]
    (i : Fin N) (f : E → ℝ) (hf : Integrable f μ) :
    ∫ φ : Fin N → E, f (φ i) ∂(nComponentMeasure N μ) =
    ∫ x, f x ∂μ := by
  -- (eval i) is measure-preserving from (pi μ) to μ by measurePreserving_eval.
  -- integral_map: ∫ y, f y ∂(map φ μ) = ∫ x, f (φ x) ∂μ
  -- So: ∫ x, f(x i) ∂(pi μ) = ∫ y, f y ∂(map (eval i) (pi μ)) = ∫ y, f y ∂μ.
  have hmeas : MeasurePreserving (Function.eval i) (nComponentMeasure N μ) μ :=
    measurePreserving_eval (fun _ : Fin N => μ) i
  rw [show (fun φ : Fin N → E => f (φ i)) = f ∘ Function.eval i from rfl]
  have step : ∫ (x : Fin N → E), (f ∘ Function.eval i) x ∂nComponentMeasure N μ =
              ∫ y, f y ∂(Measure.map (Function.eval i) (nComponentMeasure N μ)) := by
    rw [integral_map hmeas.measurable.aemeasurable]
    · rfl
    · rw [hmeas.map_eq]; exact hf.aestronglyMeasurable
  rw [step, hmeas.map_eq]

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
  -- Step 1: coordinate projections are iIndepFun under the product measure.
  -- iIndepFun_pi with Ω = fun _ => E, 𝓧 = fun _ => E, X = fun _ => id.
  have hind : iIndepFun (fun (k : Fin N) (ω : Fin N → E) => ω k)
      (nComponentMeasure N μ) := by
    have h := @iIndepFun_pi (Fin N) _ (fun _ => E) (fun _ => inferInstance)
      (fun _ => μ) (fun _ => inferInstance) (fun _ => E) (fun _ => inferInstance)
      (fun _ => id) (fun _ => aemeasurable_id)
    simp only [id] at h; exact h
  -- Step 2: pairwise independence of projections i and j.
  have hindij : IndepFun (fun ω : Fin N → E => ω i)
      (fun ω : Fin N → E => ω j) (nComponentMeasure N μ) :=
    hind.indepFun hij
  -- Step 3: measure-preserving projections (for AEStronglyMeasurable hypotheses).
  have hmeas_i : MeasurePreserving (Function.eval i) (nComponentMeasure N μ) μ :=
    measurePreserving_eval (fun _ : Fin N => μ) i
  have hmeas_j : MeasurePreserving (Function.eval j) (nComponentMeasure N μ) μ :=
    measurePreserving_eval (fun _ : Fin N => μ) j
  -- Step 4: f and g are AEStronglyMeasurable w.r.t. the respective pushforward measures.
  have hf_ae : AEStronglyMeasurable f
      (Measure.map (fun ω : Fin N → E => ω i) (nComponentMeasure N μ)) := by
    simp only [show (fun ω : Fin N → E => ω i) = Function.eval i from rfl, hmeas_i.map_eq]
    exact hf.aestronglyMeasurable
  have hg_ae : AEStronglyMeasurable g
      (Measure.map (fun ω : Fin N → E => ω j) (nComponentMeasure N μ)) := by
    simp only [show (fun ω : Fin N → E => ω j) = Function.eval j from rfl, hmeas_j.map_eq]
    exact hg.aestronglyMeasurable
  -- Step 5: integral factorization via IndepFun.integral_comp_mul_comp.
  have key := hindij.integral_comp_mul_comp
    (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable
    hf_ae hg_ae
  simp only [Function.comp, Pi.mul_apply] at key
  -- key : ∫ x, f(x i) * g(x j) ∂(pi μ) = (∫ x, f(x i) ∂(pi μ)) * (∫ x, g(x j) ∂(pi μ))
  -- Step 6: reduce each marginal to μ via nComponent_marginal.
  rw [key, nComponent_marginal N μ i f hf, nComponent_marginal N μ j g hg]

end Pphi2N

end
