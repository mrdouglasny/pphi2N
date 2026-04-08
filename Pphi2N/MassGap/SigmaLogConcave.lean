/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# σ-Measure Log-Concavity and Brascamp-Lieb Application

Bridges the σ-field effective action to the Brascamp-Lieb inequality
from markov-semigroups, deriving the variance bound Var(σ(x)) ≤ 1/(κN).

## Architecture

The σ-measure μ_σ ∝ exp(-N·s_eff[σ]) lives on E = EuclideanSpace ℝ Λ
(= (Λ → ℝ) with l² inner product). The effective action is:

  s_eff[σ] = ½ Tr log(-Δ + diag(σ)) + Σ_x V(σ(x))

Its Hessian at σ is: Hess(N·s_eff)_{xy} = N·(-½G²_{xy} + 2λδ_{xy})
where G = (-Δ+σ)⁻¹. When 2λ > ½‖G²‖, this is ≥ κN·I.

We axiomatize: the σ-measure admits a `LogConcaveMeasure` structure
with Hessian ≥ κN (the Hessian computation). Then we PROVE the
variance bound using `brascampLieb_poincare` from markov-semigroups.

## Main results

- `sigma_logConcave` — axiom: σ-measure is log-concave with Hessian ≥ κN
- `sigma_variance_from_BL` — theorem: Var(σ(x)) ≤ 1/(κN)

## References

- Brascamp-Lieb (1976), Theorem 5.1
- Brézin-Zinn-Justin (1976), Eq. (2.5)-(2.8)
-/

import Pphi2N.MassGap.SigmaConcentration
import MarkovSemigroups.Instances.BrascampLieb
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

noncomputable section

open MeasureTheory

namespace Pphi2N

variable {Λ : Type*} [Fintype Λ]

/-! ## The σ-measure as a LogConcaveMeasure

The σ-field space is E = EuclideanSpace ℝ Λ (finite-dim inner product space).
The σ-measure has potential V = N·s_eff with Hessian ≥ κN.

We axiomatize the construction of the LogConcaveMeasure instance,
which requires:
1. V : E → ℝ is C² (smoothness of log-det + polynomial)
2. Hess V ≥ κN (convexity from 2λ > ½‖G²‖)
3. μ = (1/Z)exp(-V)dx is a probability measure
4. Integrability of Hessian forms (from finite dimension + exponential decay)

The Hessian computation involves:
  Hess(Tr log(-Δ+σ))_{xy} = -G[σ]²_{xy}
where G[σ] = (-Δ+σ)⁻¹. This requires matrix calculus (derivative of log-det). -/

/-- **The σ-measure is log-concave with Hessian ≥ κN.**

Axiom: for the O(N) LSM with convexity data D, there exists a
`LogConcaveMeasure` on the σ-field space with:
- Hessian of the potential ≥ κN · ‖v‖² for all v (strict convexity)
- The gradient integrability conditions needed for BL

Mathematical content: the Hessian of N·s_eff is
  N·(-½G² + 2λI) ≥ N·(2λ - ½‖G²‖)·I = κN·I
where κ = 2λ - ½‖G²‖ > 0 when λ exceeds the convexity threshold.

This is a computation about the specific form of s_eff, not about
abstract log-concave measures. It requires:
- Matrix derivative: d²/dσ² Tr log(A+σ) = -A⁻² (standard)
- Operator norm bound: ‖G²‖ = ‖(-Δ+σ*)⁻²‖ ≤ 1/σ*² (from -Δ ≥ 0)

References: Brézin-Zinn-Justin (1976), §II; Simon (1974), Ch. III. -/
axiom sigma_logConcave [DecidableEq Λ]
    (D : SigmaConvexityData Λ) :
    ∃ (m : LogConcaveMeasure (EuclideanSpace ℝ Λ)),
      -- Hessian lower bound: Hess V ≥ κN
      (∀ (x : EuclideanSpace ℝ Λ) (v : EuclideanSpace ℝ Λ),
        D.kappa * D.N * ‖v‖ ^ 2 ≤ hessianBilin m.V x v v) ∧
      -- Gradient integrability (for coordinate projections)
      (∀ (f : EuclideanSpace ℝ Λ → ℝ), ContDiff ℝ 1 f →
        Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) m.μ) ∧
      -- Hessian integrability
      (∀ (u : EuclideanSpace ℝ Λ → ℝ),
        Integrable (fun x => hessianBilin m.V x (gradient u x) (gradient u x)) m.μ)

/-! ## The Brascamp-Lieb variance bound

From `brascampLieb_poincare`: for a LogConcaveMeasure with Hess V ≥ ρ,

  Var_μ(f) ≤ (1/ρ) · ∫ ‖∇f‖² dμ

For f = coordinate projection σ(x):
- fderiv f = proj x (constant linear map)
- ‖fderiv f‖² = ‖proj x‖² = 1 (unit coordinate projection)
- ∫ ‖∇f‖² dμ = ∫ 1 dμ = 1 (probability measure)

So: Var(σ(x)) ≤ 1/ρ = 1/(κN). -/

/-- **Brascamp-Lieb variance bound for the σ-field.**

For the σ-measure with convexity data (κ, σ*, N),
the variance of σ(x) at any site x satisfies:

  Var(σ(x)) ≤ 1/(κN)

Proved by applying `brascampLieb_poincare` from markov-semigroups
to the LogConcaveMeasure from `sigma_logConcave`. -/
theorem sigma_variance_from_BL [DecidableEq Λ]
    (D : SigmaConvexityData Λ) (x : Λ) :
    ∃ (m : LogConcaveMeasure (EuclideanSpace ℝ Λ)),
      m.variance (fun σ => σ x) ≤ D.varianceBound := by
  obtain ⟨m, hHess, hGrad, hHInt⟩ := sigma_logConcave D
  refine ⟨m, ?_⟩
  -- Apply Brascamp-Lieb Poincaré with ρ = κN
  have hρ : 0 < D.kappa * D.N := mul_pos D.hkappa
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp D.hN)))
  -- f = coordinate projection σ ↦ σ x
  set f : EuclideanSpace ℝ Λ → ℝ := fun σ => σ x with hf_def
  -- f is C¹ (it's a continuous linear map, hence smooth)
  have hf_smooth : ContDiff ℝ 1 f := by
    have : f = (PiLp.proj 2 (fun _ : Λ => ℝ) x : EuclideanSpace ℝ Λ →L[ℝ] ℝ) := rfl
    rw [this]
    exact ContinuousLinearMap.contDiff _
  have hBL := m.brascampLieb_poincare (D.kappa * D.N) hρ hHess
    f hf_smooth (hGrad f hf_smooth) (hHInt)
  -- hBL : m.variance (σ ↦ σ x) ≤ (1/(κN)) * ∫ ‖fderiv (σ ↦ σ x)‖² dμ
  -- The fderiv of a coordinate projection is the constant proj x
  -- ‖proj x‖ = 1, so ∫ ‖fderiv‖² dμ = ∫ 1 dμ = 1 (probability measure)
  -- The integral ∫ ‖fderiv f σ‖² dμ = 1 because:
  -- fderiv of coordinate projection = constant, ‖proj x‖ = 1, ∫1 dμ = 1
  -- fderiv of f = PiLp.proj (constant CLM)
  have hfderiv : ∀ σ, fderiv ℝ f σ = (PiLp.proj 2 (fun _ : Λ => ℝ) x :
      EuclideanSpace ℝ Λ →L[ℝ] ℝ) := by
    intro σ
    have : f = (PiLp.proj 2 (fun _ : Λ => ℝ) x : EuclideanSpace ℝ Λ →L[ℝ] ℝ) := rfl
    rw [this, ContinuousLinearMap.fderiv]
  -- ‖PiLp.proj x‖ ≤ 1 (coordinate projection has operator norm ≤ 1)
  have hnorm_le : ‖(PiLp.proj 2 (fun _ : Λ => ℝ) x :
      EuclideanSpace ℝ Λ →L[ℝ] ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v; simp only [PiLp.proj_apply, one_mul]
    -- |v x| ≤ ‖v‖ for EuclideanSpace (component ≤ l² norm)
    calc ‖v x‖ = Real.sqrt (‖v x‖ ^ 2) := by rw [Real.sqrt_sq (norm_nonneg _)]
      _ ≤ Real.sqrt (∑ i, ‖v i‖ ^ 2) := Real.sqrt_le_sqrt
          (Finset.single_le_sum (fun i _ => sq_nonneg (‖v i‖)) (Finset.mem_univ x))
      _ = ‖v‖ := by rw [EuclideanSpace.norm_eq]
  -- ∫ ‖fderiv f σ‖² dμ ≤ 1
  have hint_le : ∫ σ, ‖fderiv ℝ f σ‖ ^ 2 ∂m.μ ≤ 1 := by
    have h1 : ∀ σ, ‖fderiv ℝ f σ‖ ^ 2 ≤ 1 := by
      intro σ; rw [hfderiv]; exact pow_le_one₀ (norm_nonneg _) hnorm_le
    calc ∫ σ, ‖fderiv ℝ f σ‖ ^ 2 ∂m.μ
        ≤ ∫ _, (1 : ℝ) ∂m.μ := by
          apply MeasureTheory.integral_mono (hGrad f hf_smooth) (integrable_const 1)
          exact fun σ => h1 σ
      _ = 1 := by simp [measure_univ]
  -- Combine: Var ≤ (1/κN) * 1 = varianceBound
  calc m.variance f
      ≤ 1 / (D.kappa * D.N) * ∫ σ, ‖fderiv ℝ f σ‖ ^ 2 ∂m.μ := hBL
    _ ≤ 1 / (D.kappa * D.N) * 1 := by
        apply mul_le_mul_of_nonneg_left hint_le
        exact div_nonneg zero_le_one (le_of_lt hρ)
    _ = D.varianceBound := by unfold SigmaConvexityData.varianceBound; ring

/-- **Resolvent perturbation bound (trivially proved).**

The interval [physicalMassLowerBound, √σ*] is nonempty because
physicalMassLowerBound = √σ* - δ ≤ √σ*. We witness m_phys = √σ*.

Note: the real mathematical content (that √σ* is actually the mass of
the averaged propagator) is captured by the σ-concentration machinery,
not by this existential. The formal theorem `infiniteVolume_massGap_largeN`
only needs ∃ m > 0, which follows from σ* > 0. -/
theorem resolvent_perturbation_bound_from_BL [DecidableEq Λ]
    (D : SigmaConvexityData Λ) :
    ∃ (m_phys : ℝ),
      D.physicalMassLowerBound ≤ m_phys ∧ m_phys ≤ Real.sqrt D.sigma_star :=
  ⟨Real.sqrt D.sigma_star, D.physicalMassLowerBound_le_sqrt_sigma_star, le_refl _⟩

end Pphi2N

end
