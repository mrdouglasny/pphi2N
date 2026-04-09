/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# σ-Measure Log-Concavity and Brascamp-Lieb Application

Proves Var(σ(x)) ≤ 1/(κN) from the Brascamp-Lieb inequality.

## Architecture

Two axioms provide the σ-measure data:
- `sigma_lcm_exists`: LogConcaveMeasure + Hessian bound + integrability
- (`sigma_hessian_bound` was merged into `sigma_lcm_exists`)

One theorem uses them:
- `sigma_variance_from_BL`: Var(σ(x)) ≤ 1/(κN) (proved via brascampLieb_poincare)

## References

- Brascamp-Lieb (1976), Theorem 5.1
-/

import Pphi2N.MassGap.SigmaHessian
import MarkovSemigroups.Instances.BrascampLieb
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

noncomputable section

open MeasureTheory

namespace Pphi2N

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## The σ-measure axiom

This single axiom packages the LogConcaveMeasure construction:
1. V = N·s_eff is C² and strictly convex (from MatrixCalculus + SigmaHessian)
2. μ = (1/Z)exp(-V)dx is a probability measure
3. Hessian ≥ κN (from seff_hessian_lower_bound)
4. Integrability for the BL application to coordinate projections -/

/-- **The σ-measure is log-concave with Hessian ≥ κN.**

Provides a `LogConcaveMeasure` for the σ-field with:
- Hessian bound ≥ κN for all σ, v (strict convexity)
- Hessian integrability (needed by the BL resolvent axiom)

The gradient integrability for coordinate projections is PROVED
(not axiomatized) since fderiv of coord proj is constant with norm ≤ 1.

Mathematical content: construct V = N·s_eff on EuclideanSpace ℝ Λ,
show exp(-V) integrable, verify Hessian = N(-½G²+2λI) ≥ κN.
Uses: contDiff_matrix_det, seff_hessian_lower_bound. -/
axiom sigma_lcm_exists (D : SigmaConvexityData Λ) :
    ∃ (m : LogConcaveMeasure (EuclideanSpace ℝ Λ)),
      -- Hessian lower bound: Hess V ≥ κN
      (∀ (σ : EuclideanSpace ℝ Λ) (v : EuclideanSpace ℝ Λ),
        D.kappa * D.N * ‖v‖ ^ 2 ≤ hessianBilin m.V σ v v) ∧
      -- Hessian integrability (for BL resolvent axiom)
      (∀ (u : EuclideanSpace ℝ Λ → ℝ),
        Integrable (fun x => hessianBilin m.V x (gradient u x) (gradient u x)) m.μ)

/-! ## The Brascamp-Lieb variance bound -/

/-- **Var(σ(x)) ≤ 1/(κN) from Brascamp-Lieb.**

Proved from `sigma_lcm_exists` + `brascampLieb_poincare`. The gradient
integrability for f = σ(x) is proved directly: fderiv = PiLp.proj x
(constant, norm ≤ 1), so ∫ ‖fderiv‖² dμ ≤ 1 (probability measure). -/
theorem sigma_variance_from_BL
    (D : SigmaConvexityData Λ) (x : Λ) :
    ∃ (m : LogConcaveMeasure (EuclideanSpace ℝ Λ)),
      m.variance (fun σ => σ x) ≤ D.varianceBound := by
  obtain ⟨m, hHess, hHInt⟩ := sigma_lcm_exists D
  refine ⟨m, ?_⟩
  have hρ : 0 < D.kappa * D.N := mul_pos D.hkappa
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp D.hN)))
  -- f = coordinate projection σ ↦ σ x
  set f : EuclideanSpace ℝ Λ → ℝ := fun σ => σ x with hf_def
  have hf_smooth : ContDiff ℝ 1 f := by
    have : f = (PiLp.proj 2 (fun _ : Λ => ℝ) x : EuclideanSpace ℝ Λ →L[ℝ] ℝ) := rfl
    rw [this]; exact ContinuousLinearMap.contDiff _
  -- Gradient integrability: fderiv f = constant (proj x), norm ≤ 1
  have hGrad : Integrable (fun σ => ‖fderiv ℝ f σ‖ ^ 2) m.μ := by
    have hfderiv : ∀ σ, fderiv ℝ f σ = (PiLp.proj 2 (fun _ : Λ => ℝ) x :
        EuclideanSpace ℝ Λ →L[ℝ] ℝ) := by
      intro σ
      have : f = (PiLp.proj 2 (fun _ : Λ => ℝ) x : EuclideanSpace ℝ Λ →L[ℝ] ℝ) := rfl
      rw [this, ContinuousLinearMap.fderiv]
    simp_rw [hfderiv]
    exact integrable_const _
  -- Apply brascampLieb_poincare
  have hBL := m.brascampLieb_poincare (D.kappa * D.N) hρ hHess
    f hf_smooth hGrad hHInt
  -- ‖PiLp.proj x‖ ≤ 1
  have hfderiv : ∀ σ, fderiv ℝ f σ = (PiLp.proj 2 (fun _ : Λ => ℝ) x :
      EuclideanSpace ℝ Λ →L[ℝ] ℝ) := by
    intro σ
    have : f = (PiLp.proj 2 (fun _ : Λ => ℝ) x : EuclideanSpace ℝ Λ →L[ℝ] ℝ) := rfl
    rw [this, ContinuousLinearMap.fderiv]
  have hnorm_le : ‖(PiLp.proj 2 (fun _ : Λ => ℝ) x :
      EuclideanSpace ℝ Λ →L[ℝ] ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v; simp only [PiLp.proj_apply, one_mul]
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
          apply MeasureTheory.integral_mono hGrad (integrable_const 1)
          exact fun σ => h1 σ
      _ = 1 := by simp [measure_univ]
  calc m.variance f
      ≤ 1 / (D.kappa * D.N) * ∫ σ, ‖fderiv ℝ f σ‖ ^ 2 ∂m.μ := hBL
    _ ≤ 1 / (D.kappa * D.N) * 1 := by
        apply mul_le_mul_of_nonneg_left hint_le
        exact div_nonneg zero_le_one (le_of_lt hρ)
    _ = D.varianceBound := by unfold SigmaConvexityData.varianceBound; ring

/-- **Resolvent perturbation bound (trivially proved).** -/
theorem resolvent_perturbation_bound_from_BL
    (D : SigmaConvexityData Λ) :
    ∃ (m_phys : ℝ),
      D.physicalMassLowerBound ≤ m_phys ∧ m_phys ≤ Real.sqrt D.sigma_star :=
  ⟨Real.sqrt D.sigma_star, D.physicalMassLowerBound_le_sqrt_sigma_star, le_refl _⟩

end Pphi2N

end
