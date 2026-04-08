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
    (hρ_sq_int : Integrable (fun ω => ρ ω ^ 2) μ)
    (hK : ∫ ω, ρ ω ^ 2 ∂μ ≤ K) :
    ∫ ω, F ω ∂((ENNReal.ofReal Z)⁻¹ • μ.withDensity (fun ω => ENNReal.ofReal (ρ ω))) ≤
    (1 / Z) * K ^ (1/2 : ℝ) * (∫ ω, F ω ^ (2 : ℝ) ∂μ) ^ (1/2 : ℝ) := by
  -- Step 1: Unfold the smeared measure integral
  -- ∫ F d(c • ν) = c.toReal * ∫ F dν
  rw [integral_smul_measure]
  -- Step 2: Convert withDensity integral via NNReal path
  -- ∫ F d(μ.withDensity (ofReal ∘ ρ)) = ∫ ρ * F dμ
  set ρ_nn := fun ω => Real.toNNReal (ρ ω)
  have hρ_nn_meas : Measurable ρ_nn := Measurable.real_toNNReal hρ_meas
  have wd_eq : ∫ ω, F ω ∂(μ.withDensity (fun ω => ENNReal.ofReal (ρ ω))) =
      ∫ ω, ρ ω * F ω ∂μ := by
    change ∫ ω, F ω ∂(μ.withDensity (fun ω => ↑(ρ_nn ω))) =
      ∫ ω, ρ ω * F ω ∂μ
    rw [integral_withDensity_eq_integral_smul hρ_nn_meas]
    congr 1; ext ω
    simp only [ρ_nn, NNReal.smul_def, smul_eq_mul]
    rw [Real.coe_toNNReal _ (hρ_nn ω)]
  rw [wd_eq]
  -- Simplify the scalar: (ENNReal.ofReal Z)⁻¹.toReal = Z⁻¹
  have hc_real : ((ENNReal.ofReal Z)⁻¹).toReal = Z⁻¹ := by
    simp [ENNReal.toReal_inv, ENNReal.toReal_ofReal (le_of_lt hZ_pos)]
  rw [hc_real]
  -- Goal: Z⁻¹ • ∫ ρ * F dμ ≤ (1/Z) * K^{1/2} * (∫ F^2 dμ)^{1/2}
  -- Convert smul to mul for reals
  rw [smul_eq_mul]
  -- Note: Z⁻¹ = 1/Z
  have hZinv_eq : Z⁻¹ = 1 / Z := (one_div Z).symm
  rw [hZinv_eq]
  -- Suffices to bound the inner integral by Cauchy-Schwarz
  -- ∫ ρ*F ≤ (∫ ρ²)^{1/2} * (∫ F²)^{1/2} ≤ K^{1/2} * (∫ F²)^{1/2}
  -- Reassociate: (1/Z) * K^{1/2} * (∫ F²)^{1/2} = (1/Z) * (K^{1/2} * (∫ F²)^{1/2})
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg one_pos.le (le_of_lt hZ_pos))
  -- Step 3: Construct MemLp instances for Cauchy-Schwarz
  have hρ_memLp : MemLp ρ 2 μ :=
    (memLp_two_iff_integrable_sq hρ_meas.aestronglyMeasurable).mpr hρ_sq_int
  have hF_memLp : MemLp F 2 μ :=
    (memLp_two_iff_integrable_sq hF_meas).mpr hF_sq_int
  -- Apply Cauchy-Schwarz (Hölder with p = q = 2)
  have h_cs : ∫ ω, ρ ω * F ω ∂μ ≤
      (∫ ω, ρ ω ^ (2:ℝ) ∂μ) ^ (1/2 : ℝ) *
      (∫ ω, F ω ^ (2:ℝ) ∂μ) ^ (1/2 : ℝ) := by
    have h_ofReal : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by norm_num
    exact integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (ae_of_all _ fun ω => hρ_nn ω)
      (ae_of_all _ fun ω => hF_nn ω)
      (h_ofReal ▸ hρ_memLp) (h_ofReal ▸ hF_memLp)
  -- Bound (∫ ρ²)^{1/2} ≤ K^{1/2}
  have hρ_sq_le : (∫ ω, ρ ω ^ (2:ℝ) ∂μ) ^ (1/2 : ℝ) ≤ K ^ (1/2 : ℝ) := by
    apply Real.rpow_le_rpow
    · exact integral_nonneg (fun ω => Real.rpow_nonneg (hρ_nn ω) _)
    · -- ∫ ρ^{rpow 2} = ∫ ρ^{nat 2}: convert rpow to nat pow
      have : ∫ ω, ρ ω ^ (2:ℝ) ∂μ = ∫ ω, ρ ω ^ (2:ℕ) ∂μ := by
        congr 1; ext ω; exact Real.rpow_natCast _ 2
      linarith
    · linarith
  calc ∫ ω, ρ ω * F ω ∂μ
      ≤ (∫ ω, ρ ω ^ (2:ℝ) ∂μ) ^ (1/2:ℝ) * (∫ ω, F ω ^ (2:ℝ) ∂μ) ^ (1/2:ℝ) := h_cs
    _ ≤ K ^ (1/2:ℝ) * (∫ ω, F ω ^ (2:ℝ) ∂μ) ^ (1/2:ℝ) := by
        apply mul_le_mul_of_nonneg_right hρ_sq_le
        exact Real.rpow_nonneg (integral_nonneg (fun ω => Real.rpow_nonneg (hF_nn ω) _)) _

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
  -- Abbreviations
  set μ_N := nComponentMeasure N μ_scalar
  set bw := onBoltzmannWeight N d M P c a
  set Z := onPartitionFunction N d M P c a μ_scalar
  -- Measurability of the Boltzmann weight
  -- wickMonomial_ON is a polynomial in t (pair induction on k), hence continuous
  have wickMonomial_cont : ∀ k, Continuous (fun t : ℝ => wickMonomial_ON N c k t) := by
    -- Prove by pair induction: at step k, carry continuity of both k and k+1
    suffices h : ∀ k, Continuous (fun t : ℝ => wickMonomial_ON N c k t) ∧
        Continuous (fun t : ℝ => wickMonomial_ON N c (k + 1) t) from
      fun k => (h k).1
    intro k; induction k with
    | zero =>
      exact ⟨by simp [wickMonomial_ON]; exact continuous_const,
             by show Continuous (fun t : ℝ => t - ↑N * c); fun_prop⟩
    | succ k ih =>
      obtain ⟨hk, hk1⟩ := ih
      exact ⟨hk1, by
        show Continuous (fun t : ℝ =>
          (t - wickShiftCoeff N (k + 1) * c) * wickMonomial_ON N c (k + 1) t -
          wickLowerCoeff N (k + 1) * c ^ 2 * wickMonomial_ON N c k t)
        exact ((continuous_id.sub continuous_const).mul hk1).sub
          (continuous_const.mul hk)⟩
  have hbw_meas : Measurable bw := by
    unfold bw onBoltzmannWeight onInteraction
    apply Real.measurable_exp.comp
    apply Measurable.neg
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro x _
    -- wickInteraction_ON is continuous (polynomial in t), hence measurable
    unfold wickInteraction_ON
    apply Measurable.add
    · apply Measurable.const_mul
      apply (wickMonomial_cont P.degree).measurable.comp
      unfold siteNormSq; apply Finset.measurable_sum; intro i _
      exact ((measurable_pi_apply x).comp (measurable_pi_apply i)).pow_const _
    · apply Finset.measurable_sum; intro m _
      apply Measurable.const_mul
      apply (wickMonomial_cont m).measurable.comp
      unfold siteNormSq; apply Finset.measurable_sum; intro i _
      exact ((measurable_pi_apply x).comp (measurable_pi_apply i)).pow_const _
  -- Nelson bound: V(φ) ≥ -B pointwise
  obtain ⟨B, hB⟩ := onNelsonEstimate N d M P c a ha hc
  -- Boltzmann weight properties
  have hbw_pos : ∀ φ, 0 < bw φ := onBoltzmannWeight_pos N d M P c a
  have hbw_nn : ∀ φ, 0 ≤ bw φ := fun φ => le_of_lt (hbw_pos φ)
  have hbw_bound : ∀ φ, bw φ ≤ Real.exp B := fun φ =>
    Real.exp_le_exp_of_le (by linarith [hB φ])
  -- bw is integrable (bounded above by exp(B))
  have hbw_int : Integrable bw μ_N := by
    apply (memLp_of_bounded (a := 0) (b := Real.exp B)
      (ae_of_all _ (fun φ => ?_))
      hbw_meas.aestronglyMeasurable (p := 1)).integrable le_rfl
    exact ⟨le_of_lt (hbw_pos φ), hbw_bound φ⟩
  -- bw² is integrable (bounded above by exp(2B))
  have hbw_sq_int : Integrable (fun φ => bw φ ^ 2) μ_N := by
    apply Integrable.of_bound (hbw_meas.pow_const 2).aestronglyMeasurable (Real.exp B ^ 2)
    exact ae_of_all _ fun φ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_le_sq'
        (by linarith [hbw_pos φ, Real.exp_pos B])
        (hbw_bound φ)
  -- Partition function Z > 0
  have hZ_pos : 0 < Z := by
    unfold Z onPartitionFunction
    rw [integral_pos_iff_support_of_nonneg (fun φ => le_of_lt (hbw_pos φ)) hbw_int]
    have hsupport : Function.support bw = Set.univ := by
      ext φ; simp [Function.mem_support, (hbw_pos φ).ne']
    rw [hsupport, measure_univ]; norm_num
  -- Z = ∫ bw dμ_N
  have hZ_eq : ∫ φ, bw φ ∂μ_N = Z := rfl
  -- Unfold onInteractingMeasure to match density_transfer_general
  show ∫ φ, F φ ∂(onInteractingMeasure N d M P c a μ_scalar) ≤ _
  unfold onInteractingMeasure
  -- The goal now matches density_transfer_general
  exact density_transfer_general μ_N bw hbw_nn hbw_meas Z hZ_pos hZ_eq
    F hF_nn hF_meas hF_sq_int K hK_pos hbw_sq_int hK_nelson

end Pphi2N

end
