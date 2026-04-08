/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# O(N) Torus Continuum Limit and OS Axioms

Proves existence of the continuum limit and OS0-OS2 for the O(N)
interacting measure on T²_L, following pphi2's proof architecture.

## Construction

For each lattice size M, `lsmTorusMeasure L params M` is a probability
measure on the N-component continuum configuration space. As M → ∞
(lattice spacing a = L/M → 0), we extract a subsequential weak limit
via tightness + Prokhorov.

## OS Axioms

- **OS0 (Analyticity)**: from exponential moment domination via
  `analyticOnNhd_integral`, same as pphi2
- **OS1 (Regularity)**: from the Nelson exponential moment bound
- **OS2 (Translation invariance)**: the O(N) interaction Σ_x :P(|φ(x)|²):
  is invariant under lattice translations; torus equivariance transfers
  to the continuum limit

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I-II
- Glimm-Jaffe, *Quantum Physics*, Ch. 6, 19
-/

import Pphi2N.ContinuumLimit.LSMTorusMeasure
import Pphi2N.ContinuumLimit.EmbeddingBound
import Pphi2.GeneralResults.ComplexAnalysis
import GaussianField.Tightness
import GaussianField.ConfigurationEmbedding
import Torus.Symmetry
import Nuclear.TensorProductFunctorAxioms

noncomputable section

open GaussianField MeasureTheory Filter ComplexAnalysis

namespace Pphi2N

variable (L_phys : ℝ) [hL : Fact (0 < L_phys)]

-- LSMParams has hN : 1 ≤ N, from which we derive NeZero N.
private def neZeroOfLSM (params : LSMParams) : NeZero params.N :=
  ⟨Nat.one_le_iff_ne_zero.mp params.hN⟩

attribute [local instance] neZeroOfLSM

/-! ## Uniform second moment bound

The key tightness input: for each test function f, the second moment
∫ (ω f)² dμ_M is bounded uniformly in M. This follows from:
1. Nelson estimate: the interacting measure's moments are controlled
   by the Gaussian moments (density transfer via Cauchy-Schwarz)
2. Gaussian second moment = G(f,f) where G is the Green's function
3. G(f,f) is bounded by a continuous seminorm of f (operator bound) -/

/-- **Uniform density transfer constant (textbook axiom).**

For nonneg F measurable on the lattice field:
  ∫ F d(onInteractingMeasure) ≤ D * ∫ F d(nComponentMeasure GFF)

where D is a positive constant independent of M. The ratio exp(B)/Z satisfies:
- B = L^d * |C_P| (Nelson bound, uniform in M since a^d * |Λ| = L^d)
- Z = E[exp(-V)] ≥ 1 (Jensen's inequality + E_GFF[V] ≤ 0 for Wick-ordered V)

Hence exp(B)/Z ≤ exp(B), a constant independent of M. -/
axiom lsmDensityTransferConstant (params : LSMParams) :
    ∃ (D : ℝ), 0 < D ∧
      ∀ (M : ℕ) [NeZero M]
        (F : (Fin params.N → FinLatticeField 2 M) → ℝ),
        (∀ φ, 0 ≤ F φ) → Measurable F →
        Integrable F (nComponentMeasure params.N
          (scalarLatticeGFF params.mass (L_phys / M)
            (div_pos hL.out (Nat.cast_pos.mpr (NeZero.pos M))) params.hmass M)) →
        Integrable F (onInteractingMeasure params.N 2 M
          params.toONModel.interaction
          (latticeWickConstant (L_phys / M) params.mass
            (div_pos hL.out (Nat.cast_pos.mpr (NeZero.pos M))) params.hmass M)
          (L_phys / M)
          (scalarLatticeGFF params.mass (L_phys / M)
            (div_pos hL.out (Nat.cast_pos.mpr (NeZero.pos M))) params.hmass M)) ∧
        ∫ φ, F φ ∂(onInteractingMeasure params.N 2 M
          params.toONModel.interaction
          (latticeWickConstant (L_phys / M) params.mass
            (div_pos hL.out (Nat.cast_pos.mpr (NeZero.pos M))) params.hmass M)
          (L_phys / M)
          (scalarLatticeGFF params.mass (L_phys / M)
            (div_pos hL.out (Nat.cast_pos.mpr (NeZero.pos M))) params.hmass M)) ≤
        D * ∫ φ, F φ ∂(nComponentMeasure params.N
          (scalarLatticeGFF params.mass (L_phys / M)
            (div_pos hL.out (Nat.cast_pos.mpr (NeZero.pos M))) params.hmass M))

theorem lsmTorus_uniform_second_moment (params : LSMParams) :
    ∃ (C : ℝ) (q : NComponentTorusTestFunction L_phys params.N → ℝ),
      0 < C ∧ Continuous q ∧
      ∀ (M : ℕ) [NeZero M] (f : NComponentTorusTestFunction L_phys params.N),
        ∫ ω : NComponentTorusConfig L_phys params.N,
          (ω f) ^ 2 ∂(lsmTorusMeasure L_phys params M) ≤ C * q f ^ 2 := by
  -- Get GFF bound from the axiom
  obtain ⟨C_gff, q_gff, hC_gff, hq_cont, h_gff_bound⟩ :=
    nComponentGreen_uniform_bound L_phys params.N params.mass params.hmass
  -- Get density transfer constant
  obtain ⟨D, hD_pos, h_density⟩ := lsmDensityTransferConstant L_phys params
  -- Combined constant: D * C_gff
  refine ⟨D * C_gff, q_gff, mul_pos hD_pos hC_gff, hq_cont, fun M _ f => ?_⟩
  -- Abbreviations
  set sp := L_phys / (M : ℝ)
  have hsp : 0 < sp := div_pos hL.out (Nat.cast_pos.mpr (NeZero.pos M))
  set μ_sc := scalarLatticeGFF params.mass sp hsp params.hmass M
  set μ_N := nComponentMeasure params.N μ_sc
  set embed := nComponentTorusEmbedLift L_phys params.N M
  -- Step 1: lsmTorusMeasure = Measure.map embed (onInteractingMeasure ...)
  -- Pull ∫ (ωf)² through the map
  have hembed_meas : Measurable embed := nComponentTorusEmbedLift_measurable L_phys params.N M
  have heval_meas : Measurable (fun ω : NComponentTorusConfig L_phys params.N => (ω f) ^ 2) :=
    (configuration_eval_measurable f).pow_const 2
  -- ∫ (ωf)² d(map embed ν) = ∫ (embed(φ)(f))² dν
  have h_map_int : ∫ ω, (ω f) ^ 2 ∂(lsmTorusMeasure L_phys params M) =
      ∫ φ, (embed φ f) ^ 2 ∂(onInteractingMeasure params.N 2 M
        params.toONModel.interaction
        (latticeWickConstant sp params.mass hsp params.hmass M) sp μ_sc) := by
    show ∫ ω, (ω f) ^ 2 ∂(Measure.map embed
      (onInteractingMeasure params.N 2 M params.toONModel.interaction
        (latticeWickConstant sp params.mass hsp params.hmass M) sp μ_sc)) = _
    rw [integral_map hembed_meas.aemeasurable heval_meas.aestronglyMeasurable]
  rw [h_map_int]
  -- Step 2: Apply density transfer: ∫ F dμ_int ≤ D * ∫ F dμ_N
  have hF_nn : ∀ φ, 0 ≤ (embed φ f) ^ 2 := fun φ => sq_nonneg _
  have hF_meas : Measurable (fun φ => (embed φ f) ^ 2) :=
    ((configuration_eval_measurable f).comp hembed_meas).pow_const 2
  -- GFF integrability of (embed φ f)² (same as in lsmTorus_tight)
  have hF_int_gff : Integrable (fun φ => (embed φ f) ^ 2) μ_N := by
    -- The same proof as in lsmTorus_tight (lines 210-297)
    -- Reduce to scalar GFF L² via Cauchy-Schwarz + projection
    let C_f : ℝ := ∑ x : FinLatticeSites 2 M, ∑ i : Fin params.N,
        (evalNComponentAtSite L_phys params.N M x i f) ^ 2
    have hC_f_nn : 0 ≤ C_f := Finset.sum_nonneg fun x _ =>
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hcs : ∀ φ : Fin params.N → FinLatticeField 2 M,
        (embed φ f) ^ 2 ≤ C_f * (∑ x, ∑ i, (φ i x) ^ 2) := by
      intro φ
      show (∑ x, ∑ i, φ i x * evalNComponentAtSite L_phys params.N M x i f) ^ 2 ≤ _
      have key := Finset.sum_mul_sq_le_sq_mul_sq
        (Finset.univ (α := FinLatticeSites 2 M × Fin params.N))
        (fun xi => evalNComponentAtSite L_phys params.N M xi.1 xi.2 f)
        (fun xi => φ xi.2 xi.1)
      have hlhs : ∑ x : FinLatticeSites 2 M, ∑ i : Fin params.N,
          φ i x * evalNComponentAtSite L_phys params.N M x i f =
          ∑ xi ∈ Finset.univ (α := FinLatticeSites 2 M × Fin params.N),
          evalNComponentAtSite L_phys params.N M xi.1 xi.2 f * φ xi.2 xi.1 := by
        rw [← Finset.univ_product_univ, Finset.sum_product]
        congr 1; ext x; congr 1; ext i; ring
      have hrhs1 : C_f = ∑ xi ∈ Finset.univ (α := FinLatticeSites 2 M × Fin params.N),
          (evalNComponentAtSite L_phys params.N M xi.1 xi.2 f) ^ 2 := by
        simp only [C_f, ← Finset.univ_product_univ, Finset.sum_product]
      have hrhs2 : ∑ x : FinLatticeSites 2 M, ∑ i : Fin params.N, (φ i x) ^ 2 =
          ∑ xi ∈ Finset.univ (α := FinLatticeSites 2 M × Fin params.N), (φ xi.2 xi.1) ^ 2 := by
        rw [← Finset.univ_product_univ, Finset.sum_product]
      rw [hlhs, hrhs1, hrhs2]; linarith [key]
    have h_scalar_int : ∀ x : FinLatticeSites 2 M,
        Integrable (fun ψ : FinLatticeField 2 M => ψ x ^ 2) μ_sc := by
      intro x
      have hμ_sc_eq : μ_sc = (latticeGaussianMeasure 2 M sp params.mass hsp params.hmass).map
          (evalMapMeasurableEquiv 2 M) := rfl
      rw [hμ_sc_eq]
      apply (integrable_map_measure
        ((measurable_pi_apply x).pow_const 2).aestronglyMeasurable
        (evalMapMeasurableEquiv 2 M).measurable.aemeasurable).mpr
      have heq : ((fun ψ : FinLatticeField 2 M => ψ x ^ 2) ∘
          (evalMapMeasurableEquiv 2 M : Configuration (FinLatticeField 2 M) →
            FinLatticeField 2 M)) =
          fun ω => (ω (finLatticeDelta 2 M x)) ^ 2 := by
        ext ω; simp [evalMapMeasurableEquiv, evalMap]
      rw [heq]
      exact (pairing_memLp (latticeCovariance 2 M sp params.mass hsp params.hmass)
        (finLatticeDelta 2 M x) 2).integrable_sq
    have h_comp_int : ∀ (x : FinLatticeSites 2 M) (i : Fin params.N),
        Integrable (fun φ : Fin params.N → FinLatticeField 2 M => (φ i x) ^ 2) μ_N := by
      intro x i
      haveI : IsProbabilityMeasure μ_sc := scalarLatticeGFF_isProbability
        params.mass sp hsp params.hmass M
      exact (measurePreserving_eval (fun _ : Fin params.N => μ_sc) i).integrable_comp_of_integrable
        (h_scalar_int x)
    exact ((integrable_finset_sum _ fun x _ => integrable_finset_sum _ fun i _ =>
      h_comp_int x i).const_mul C_f).mono
      (hF_meas.aestronglyMeasurable)
      (ae_of_all _ fun φ => by
        rw [Real.norm_of_nonneg (hF_nn φ),
            Real.norm_of_nonneg (mul_nonneg hC_f_nn (Finset.sum_nonneg fun x _ =>
              Finset.sum_nonneg fun i _ => sq_nonneg _))]
        exact hcs φ)
  calc ∫ φ, (embed φ f) ^ 2 ∂(onInteractingMeasure params.N 2 M
          params.toONModel.interaction
          (latticeWickConstant sp params.mass hsp params.hmass M) sp μ_sc)
      ≤ D * ∫ φ, (embed φ f) ^ 2 ∂μ_N :=
        (h_density M (fun φ => (embed φ f) ^ 2) hF_nn hF_meas hF_int_gff).2
    _ = D * ∫ ω, (ω f) ^ 2 ∂(Measure.map embed μ_N) := by
        congr 1
        rw [integral_map hembed_meas.aemeasurable heval_meas.aestronglyMeasurable]
    _ ≤ D * (C_gff * q_gff f ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hD_pos.le
        exact h_gff_bound M f
    _ = D * C_gff * q_gff f ^ 2 := by ring

/-! ## Tightness and Prokhorov extraction -/

/-- The sequence of LSM torus measures is tight.

Proof: uniform second moments + Mitoma-Chebyshev criterion
(from gaussian-field's `configuration_tight_of_uniform_second_moments`).
The DyninMityaginSpace instance on NComponentTorusTestFunction enables
the tightness criterion. -/
theorem lsmTorus_tight (params : LSMParams) :
    ∀ ε : ℝ, 0 < ε →
      ∃ K : Set (NComponentTorusConfig L_phys params.N),
        IsCompact K ∧ ∀ (M : ℕ) [NeZero M],
          1 - ε ≤ ((lsmTorusMeasure L_phys params M) K).toReal := by
  intro ε hε
  obtain ⟨C, q, hC, hq_cont, h_bound⟩ := lsmTorus_uniform_second_moment L_phys params
  -- Apply Mitoma-Chebyshev with ι = {M : ℕ // 0 < M}
  obtain ⟨K, hK_compact, hK_bound⟩ := configuration_tight_of_uniform_second_moments
    (ι := {M : ℕ // 0 < M})
    (fun ⟨M, hM⟩ => haveI : NeZero M := ⟨by omega⟩;
      lsmTorusMeasure L_phys params M)
    (fun ⟨M, hM⟩ => by haveI : NeZero M := ⟨by omega⟩; exact inferInstance)
    (fun f ⟨M, hM⟩ => by
      haveI : NeZero M := ⟨by omega⟩
      -- Push through the Measure.map to reduce to lattice integrability
      change Integrable (fun ω : NComponentTorusConfig L_phys params.N => (ω f) ^ 2)
        (lsmTorusMeasure L_phys params M)
      -- Unfold lsmTorusMeasure = Measure.map embed (onInteractingMeasure)
      unfold lsmTorusMeasure nComponentTorusMeasure
      have hspacing : 0 < L_phys / (M : ℝ) :=
        div_pos hL.out (Nat.cast_pos.mpr (NeZero.pos M))
      set sp := L_phys / (M : ℝ) with hsp
      set P' := params.toONModel.interaction
      set c' := latticeWickConstant sp params.mass hspacing params.hmass M
      have hc' : 0 < c' := latticeWickConstant_pos sp params.mass hspacing params.hmass M
      set μ_sc := scalarLatticeGFF params.mass sp hspacing params.hmass M
      -- After integrable_map_measure: Integrable (F ∘ embed) (onInteractingMeasure)
      rw [integrable_map_measure
        ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable
        (nComponentTorusEmbedLift_measurable L_phys params.N M).aemeasurable]
      -- Abbreviations for the interacting measure components
      set μ_N := nComponentMeasure params.N μ_sc
      set bw := onBoltzmannWeight params.N 2 M P' c' sp
      set Z := onPartitionFunction params.N 2 M P' c' sp μ_sc
      -- Nelson bound: bw φ ≤ exp(B) for all φ
      obtain ⟨B, hB⟩ := onNelsonEstimate params.N 2 M P' c' sp hspacing hc'
      have hbw_pos : ∀ φ, 0 < bw φ := onBoltzmannWeight_pos params.N 2 M P' c' sp
      have hbw_bound : ∀ φ, bw φ ≤ Real.exp B :=
        fun φ => Real.exp_le_exp_of_le (by linarith [hB φ])
      -- Measurability of the Boltzmann weight
      -- First: local proof that wickMonomial_ON N c k is continuous in t (polynomial)
      have wickMonomial_cont : ∀ k, Continuous (fun t : ℝ => wickMonomial_ON params.N c' k t) := by
        suffices h : ∀ k, Continuous (fun t : ℝ => wickMonomial_ON params.N c' k t) ∧
            Continuous (fun t : ℝ => wickMonomial_ON params.N c' (k + 1) t) from
          fun k => (h k).1
        intro k; induction k with
        | zero =>
          exact ⟨by simp [wickMonomial_ON]; exact continuous_const,
                 by show Continuous (fun t : ℝ => t - ↑params.N * c'); fun_prop⟩
        | succ k ih =>
          obtain ⟨hk, hk1⟩ := ih
          exact ⟨hk1, by
            show Continuous (fun t : ℝ =>
              (t - wickShiftCoeff params.N (k + 1) * c') * wickMonomial_ON params.N c' (k + 1) t -
              wickLowerCoeff params.N (k + 1) * c' ^ 2 * wickMonomial_ON params.N c' k t)
            exact ((continuous_id.sub continuous_const).mul hk1).sub
              (continuous_const.mul hk)⟩
      have hbw_meas : Measurable bw := by
        unfold bw onBoltzmannWeight onInteraction
        apply Real.measurable_exp.comp
        apply Measurable.neg
        apply Measurable.const_mul
        apply Finset.measurable_sum; intro x _
        -- wickInteraction_ON is continuous (polynomial in t), hence measurable
        unfold wickInteraction_ON
        apply Measurable.add
        · apply Measurable.const_mul
          apply (wickMonomial_cont P'.degree).measurable.comp
          unfold siteNormSq; apply Finset.measurable_sum; intro i _
          exact ((measurable_pi_apply x).comp (measurable_pi_apply i)).pow_const _
        · apply Finset.measurable_sum; intro m _
          apply Measurable.const_mul
          apply (wickMonomial_cont m).measurable.comp
          unfold siteNormSq; apply Finset.measurable_sum; intro i _
          exact ((measurable_pi_apply x).comp (measurable_pi_apply i)).pow_const _
      -- Integrability of bw under μ_N (bounded by exp(B))
      have hbw_int : Integrable bw μ_N :=
        Integrable.of_bound hbw_meas.aestronglyMeasurable (Real.exp B)
          (ae_of_all _ fun φ => by
            rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (hbw_pos φ))]; exact hbw_bound φ)
      -- Partition function Z > 0
      have hZ_pos : 0 < Z := by
        unfold Z onPartitionFunction
        rw [integral_pos_iff_support_of_nonneg (fun φ => le_of_lt (hbw_pos φ)) hbw_int]
        have : Function.support bw = Set.univ := by
          ext φ; simp [Function.mem_support, (hbw_pos φ).ne']
        rw [this, measure_univ]; norm_num
      -- Step 1: Reduce from (1/Z)•(withDensity bw μ_N) to withDensity bw μ_N
      -- Integrability under withDensity is the main goal:
      suffices h : Integrable ((fun ω : NComponentTorusConfig L_phys params.N => (ω f) ^ 2) ∘
          nComponentTorusEmbedLift L_phys params.N M)
          (μ_N.withDensity (fun φ => ENNReal.ofReal (bw φ))) by
        unfold onInteractingMeasure
        exact h.smul_measure (ENNReal.inv_ne_top.mpr ((ENNReal.ofReal_pos.mpr hZ_pos).ne'))
      -- Step 2: Apply integrable_withDensity_iff to reduce to μ_N
      have hdens_meas : Measurable (fun φ : Fin params.N → FinLatticeField 2 M =>
          ENNReal.ofReal (bw φ)) :=
        ENNReal.measurable_ofReal.comp hbw_meas
      apply (integrable_withDensity_iff hdens_meas
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
      -- Simplify (ENNReal.ofReal (bw φ)).toReal = bw φ
      have hbw_toReal : ∀ φ : Fin params.N → FinLatticeField 2 M,
          (ENNReal.ofReal (bw φ)).toReal = bw φ :=
        fun φ => ENNReal.toReal_ofReal (le_of_lt (hbw_pos φ))
      simp_rw [Function.comp, hbw_toReal]
      -- Goal: Integrable (fun φ => (nComponentTorusEmbedLift φ f)^2 * bw φ) μ_N
      -- Step 3: GFF integrability of the embedding squared (under the N-component GFF)
      have hembed_meas : Measurable (fun φ : Fin params.N → FinLatticeField 2 M =>
          nComponentTorusEmbedLift L_phys params.N M φ f) :=
        (configuration_eval_measurable f).comp (nComponentTorusEmbedLift_measurable L_phys params.N M)
      have h_gff_int : Integrable (fun φ : Fin params.N → FinLatticeField 2 M =>
          (nComponentTorusEmbedLift L_phys params.N M φ f) ^ 2) μ_N := by
        -- nComponentTorusEmbedLift φ f = Σ_{x,i} φ i x * c_{xi} (c_{xi} = evalNComponentAtSite x i f)
        -- Cauchy-Schwarz: (Σ a_k * b_k)^2 ≤ (Σ a_k^2) * (Σ b_k^2)
        -- gives: (embed φ f)^2 ≤ C_f * Σ_{x,i} (φ i x)^2  where C_f = Σ c_{xi}^2
        -- Then: each (φ i x)^2 is integrable under μ_N via measurePreserving_eval + scalar GFF L²
        -- Step A: Cauchy-Schwarz bound
        let C_f : ℝ := ∑ x : FinLatticeSites 2 M, ∑ i : Fin params.N,
            (evalNComponentAtSite L_phys params.N M x i f) ^ 2
        have hC_f_nn : 0 ≤ C_f := Finset.sum_nonneg fun x _ =>
          Finset.sum_nonneg fun i _ => sq_nonneg _
        have hcs : ∀ φ : Fin params.N → FinLatticeField 2 M,
            (nComponentTorusEmbedLift L_phys params.N M φ f) ^ 2 ≤
            C_f * (∑ x : FinLatticeSites 2 M, ∑ i : Fin params.N, (φ i x) ^ 2) := by
          intro φ
          -- Unfold the embedding to a double sum and apply Cauchy-Schwarz
          show (∑ x : FinLatticeSites 2 M, ∑ i : Fin params.N,
              φ i x * evalNComponentAtSite L_phys params.N M x i f) ^ 2 ≤ _
          -- Rewrite double sum as single sum over product type, apply Cauchy-Schwarz
          -- Use Finset.sum_product to flatten sums
          -- Apply Cauchy-Schwarz directly on the product type
          -- (Σ_{x,i} a_{xi} * b_{xi})^2 ≤ (Σ_{x,i} a_{xi}^2) * (Σ_{x,i} b_{xi}^2)
          have key := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ (α := FinLatticeSites 2 M × Fin params.N))
            (fun xi => evalNComponentAtSite L_phys params.N M xi.1 xi.2 f)
            (fun xi => φ xi.2 xi.1)
          -- The LHS "show" unfolded as Σ_{x} Σ_{i} φ i x * c_{xi}; reorganize
          have hlhs : ∑ x : FinLatticeSites 2 M, ∑ i : Fin params.N,
              φ i x * evalNComponentAtSite L_phys params.N M x i f =
              ∑ xi ∈ Finset.univ (α := FinLatticeSites 2 M × Fin params.N),
              evalNComponentAtSite L_phys params.N M xi.1 xi.2 f * φ xi.2 xi.1 := by
            rw [← Finset.univ_product_univ, Finset.sum_product]
            congr 1; ext x; congr 1; ext i; ring
          have hrhs1 : C_f = ∑ xi ∈ Finset.univ (α := FinLatticeSites 2 M × Fin params.N),
              (evalNComponentAtSite L_phys params.N M xi.1 xi.2 f) ^ 2 := by
            simp only [C_f, ← Finset.univ_product_univ, Finset.sum_product]
          have hrhs2 : ∑ x : FinLatticeSites 2 M, ∑ i : Fin params.N, (φ i x) ^ 2 =
              ∑ xi ∈ Finset.univ (α := FinLatticeSites 2 M × Fin params.N), (φ xi.2 xi.1) ^ 2 := by
            rw [← Finset.univ_product_univ, Finset.sum_product]
          rw [hlhs, hrhs1, hrhs2]
          linarith [key]
        -- Step B: Scalar GFF L² integrability: (ψ x)^2 integrable under μ_sc
        let μ_GFF := latticeGaussianMeasure 2 M sp params.mass hspacing params.hmass
        let T := latticeCovariance 2 M sp params.mass hspacing params.hmass
        have h_scalar_int : ∀ x : FinLatticeSites 2 M,
            Integrable (fun ψ : FinLatticeField 2 M => ψ x ^ 2) μ_sc := by
          intro x
          -- μ_sc = μ_GFF.map (evalMapMeasurableEquiv 2 M), so use integrable_map_measure
          have hμ_sc_eq : μ_sc = μ_GFF.map (evalMapMeasurableEquiv 2 M) := rfl
          rw [hμ_sc_eq]
          apply (integrable_map_measure
            ((measurable_pi_apply x).pow_const 2).aestronglyMeasurable
            (evalMapMeasurableEquiv 2 M).measurable.aemeasurable).mpr
          -- Goal: Integrable ((fun ψ => ψ x ^ 2) ∘ evalMapMeasurableEquiv 2 M) μ_GFF
          -- Simplify: (evalMapMeasurableEquiv ω x) = ω (finLatticeDelta x) by definition
          have heq : ((fun ψ : FinLatticeField 2 M => ψ x ^ 2) ∘
              (evalMapMeasurableEquiv 2 M : Configuration (FinLatticeField 2 M) →
                FinLatticeField 2 M)) =
              fun ω => (ω (finLatticeDelta 2 M x)) ^ 2 := by
            ext ω; simp [evalMapMeasurableEquiv, evalMap]
          rw [heq]
          exact (pairing_memLp T (finLatticeDelta 2 M x) 2).integrable_sq
        -- Step C: (φ i x)^2 is integrable under μ_N via measure-preserving projection
        have h_comp_int : ∀ (x : FinLatticeSites 2 M) (i : Fin params.N),
            Integrable (fun φ : Fin params.N → FinLatticeField 2 M => (φ i x) ^ 2) μ_N := by
          intro x i
          haveI h_prob_sc : IsProbabilityMeasure μ_sc := scalarLatticeGFF_isProbability
            params.mass sp hspacing params.hmass M
          -- measurePreserving_eval: (Measure.pi (fun _ => μ_sc)).map (eval i) = μ_sc
          have hmp_i : MeasurePreserving (fun φ : Fin params.N → FinLatticeField 2 M => φ i)
              μ_N μ_sc := by
            have h : MeasurePreserving (Function.eval i)
                (Measure.pi (fun _ : Fin params.N => μ_sc)) μ_sc :=
              haveI : ∀ j : Fin params.N, IsProbabilityMeasure ((fun _ : Fin params.N => μ_sc) j) :=
                fun _ => h_prob_sc
              measurePreserving_eval (fun _ : Fin params.N => μ_sc) i
            exact h
          exact hmp_i.integrable_comp_of_integrable (h_scalar_int x)
        -- Step D: finite sum of integrable functions is integrable
        have hsum_int : Integrable (fun φ : Fin params.N → FinLatticeField 2 M =>
            ∑ x : FinLatticeSites 2 M, ∑ i : Fin params.N, (φ i x) ^ 2) μ_N :=
          integrable_finset_sum _ fun x _ => integrable_finset_sum _ fun i _ => h_comp_int x i
        -- Step E: dominate (embed φ f)^2 ≤ C_f * (Σ (φ i x)^2), conclude integrability
        apply (hsum_int.const_mul C_f).mono
        · exact (hembed_meas.pow_const 2).aestronglyMeasurable
        · exact ae_of_all _ fun φ => by
            have h1 : 0 ≤ (nComponentTorusEmbedLift L_phys params.N M φ) f ^ 2 := sq_nonneg _
            have h2 : 0 ≤ ∑ x : FinLatticeSites 2 M, ∑ i : Fin params.N, (φ i x) ^ 2 :=
              Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun i _ => sq_nonneg _
            rw [Real.norm_of_nonneg h1, Real.norm_of_nonneg (mul_nonneg hC_f_nn h2)]
            exact hcs φ
      -- Step 4: Bound (embedding)^2 * bw ≤ (embedding)^2 * exp(B), use Nelson
      apply (h_gff_int.mul_const (Real.exp B)).mono
      · exact (hembed_meas.pow_const 2).aestronglyMeasurable.mul hbw_meas.aestronglyMeasurable
      · exact ae_of_all _ fun φ => by
          simp only [Real.norm_eq_abs]
          have h1 : 0 ≤ (nComponentTorusEmbedLift L_phys params.N M φ) f ^ 2 := sq_nonneg _
          rw [abs_of_nonneg (mul_nonneg h1 (le_of_lt (hbw_pos φ))),
              abs_of_nonneg (mul_nonneg h1 (le_of_lt (Real.exp_pos B)))]
          exact mul_le_mul_of_nonneg_left (hbw_bound φ) h1)
    (fun f => ⟨C * q f ^ 2,
      fun ⟨M, hM⟩ => by haveI : NeZero M := ⟨by omega⟩; exact h_bound M f⟩)
    ε hε
  exact ⟨K, hK_compact, fun M inst =>
    hK_bound ⟨M, Nat.pos_of_ne_zero (NeZero.ne M)⟩⟩

/-- **The O(N) torus continuum limit exists.**

There exists a subsequence M_n → ∞ and a probability measure μ on the
N-component continuum configuration space such that the lattice measures
converge weakly to μ. -/
theorem lsmTorusLimit_exists (params : LSMParams) :
    ∃ (μ : Measure (NComponentTorusConfig L_phys params.N)),
      IsProbabilityMeasure μ ∧
      -- BC weak convergence from a subsequence of lattice measures,
      -- with the subsequence φ explicitly available for OS2
      (∃ (φ : ℕ → ℕ), StrictMono φ ∧
        ∀ g : NComponentTorusConfig L_phys params.N → ℝ,
          Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
          Tendsto (fun n => ∫ ω, g ω
            ∂(haveI : NeZero (φ n + 1) := ⟨Nat.succ_ne_zero _⟩
              lsmTorusMeasure L_phys params (φ n + 1)))
            atTop (nhds (∫ ω, g ω ∂μ))) := by
  -- Define the ℕ-indexed sequence: n ↦ lsmTorusMeasure (n+1)
  -- (n+1 ensures NeZero)
  set μseq : ℕ → Measure (NComponentTorusConfig L_phys params.N) :=
    fun n => haveI : NeZero (n + 1) := ⟨by omega⟩;
      lsmTorusMeasure L_phys params (n + 1) with hμseq_def
  have hμseq_prob : ∀ n, IsProbabilityMeasure (μseq n) := by
    intro n; simp only [μseq]; haveI : NeZero (n + 1) := ⟨by omega⟩
    exact inferInstance
  -- Tightness of the sequence (from lsmTorus_tight, reindexed)
  have hμseq_tight : ∀ ε : ℝ, 0 < ε →
      ∃ K : Set (NComponentTorusConfig L_phys params.N),
        IsCompact K ∧ ∀ n, 1 - ε ≤ ((μseq n) K).toReal := by
    intro ε hε
    obtain ⟨K, hK, hK_bound⟩ := lsmTorus_tight L_phys params ε hε
    exact ⟨K, hK, fun n => by
      simp only [μseq]; haveI : NeZero (n + 1) := ⟨by omega⟩
      exact hK_bound (n + 1)⟩
  -- Apply Prokhorov: extract subsequence + limit
  obtain ⟨φ, ν, hφ, hν_prob, hν_conv⟩ :=
    prokhorov_configuration μseq hμseq_prob hμseq_tight
  refine ⟨ν, hν_prob, ⟨fun n => φ n, hφ, fun g hg hbdd => ?_⟩⟩
  -- hν_conv gives convergence of μseq (φ n), which equals lsmTorusMeasure (φ n + 1)
  exact hν_conv g hg hbdd

/-! ## Analyticity under the integral sign

Uses `analyticOnNhd_integral` from pphi2's GeneralResults/ComplexAnalysis.lean
(proved via dominated convergence + Hartogs). -/

/-! ## OS0 helper lemmas -/

/-- On a compact set K ⊆ (Fin n → ℂ), imaginary parts are uniformly bounded. -/
private lemma compact_im_bound {n : ℕ} {K : Set (Fin n → ℂ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ i : Fin n, |Complex.im (z i)| ≤ C := by
  by_cases hKe : K.Nonempty
  · obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
    exact ⟨M, le_trans (norm_nonneg _) (hM _ hKe.some_mem), fun z hz i =>
      (Complex.abs_im_le_norm (z i)).trans ((norm_le_pi_norm z i).trans (hM z hz))⟩
  · exact ⟨0, le_refl _, fun z hz => absurd ⟨z, hz⟩ hKe⟩

/-- For aᵢ ≥ 0: exp(c · Σ aᵢ) ≤ Σ exp(n·c·aᵢ). -/
private lemma exp_mul_sum_le' {n : ℕ} (hn : 0 < n) (c : ℝ) (hc : 0 ≤ c)
    (a : Fin n → ℝ) :
    Real.exp (c * ∑ i : Fin n, a i) ≤
    ∑ i : Fin n, Real.exp (↑n * c * a i) := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  set M := Finset.univ.sup' hne a
  have hM : ∀ i, a i ≤ M := fun i => Finset.le_sup' a (Finset.mem_univ i)
  have h_sum_le : ∑ i : Fin n, a i ≤ ↑n * M :=
    (Finset.sum_le_sum (fun i _ => hM i)).trans
      (by simp [Finset.sum_const, nsmul_eq_mul])
  have h1 : Real.exp (c * ∑ i, a i) ≤ Real.exp (↑n * c * M) :=
    Real.exp_le_exp_of_le (by nlinarith)
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' hne a
  exact h1.trans ((congr_arg Real.exp (by rw [← hj])).le.trans
    (Finset.single_le_sum (f := fun i => Real.exp (↑n * c * a i))
      (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ j)))

/-! ## OS Axioms for the continuum limit -/

/-- **OS0: Analyticity of the generating functional.**

The generating functional Z[z₁J₁ + ... + zₙJₙ] is entire analytic
in z ∈ ℂⁿ for any test functions J₁,...,Jₙ.

Proof: `analyticOnNhd_integral` with exponential moment domination,
identical to pphi2's `cylinderIR_os0` / `asymTorusInteracting_os0`.
The exponential moments of the limit measure follow from the uniform
bounds via BC convergence + truncation/MCT (same as pphi2). -/
theorem lsmTorusLimit_os0 (params : LSMParams)
    (μ : Measure (NComponentTorusConfig L_phys params.N))
    [IsProbabilityMeasure μ]
    -- The limit measure has exponential moments (from uniform bounds + weak convergence)
    (h_exp : ∀ f : NComponentTorusTestFunction L_phys params.N,
      Integrable (fun ω : NComponentTorusConfig L_phys params.N =>
        Real.exp (|ω f|)) μ)
    (n : ℕ) (J : Fin n → NComponentTorusTestFunction L_phys params.N) :
    AnalyticOnNhd ℂ (fun z : Fin n → ℂ =>
      ∫ ω, Complex.exp (∑ i, Complex.I * z i * ↑(ω (J i))) ∂μ) Set.univ := by
  apply analyticOnNhd_integral
  · -- Pointwise analyticity: z ↦ exp(Σ i·zⱼ·ω(Jⱼ)) is entire for each ω
    intro ω z _
    apply AnalyticAt.cexp'
    apply Finset.analyticAt_fun_sum
    intro i _
    exact (analyticAt_const.mul
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt z)).mul
      analyticAt_const
  · -- Measurability: F(z, ·) is ae strongly measurable for each z
    intro z
    apply (Complex.measurable_exp.comp _).aestronglyMeasurable
    exact Finset.measurable_sum Finset.univ (fun i _ =>
      measurable_const.mul
        (Complex.measurable_ofReal.comp (configuration_eval_measurable (J i))))
  · -- Domination: on compact K, ‖F(z, ω)‖ ≤ bound(ω), bound integrable
    intro K hK
    obtain ⟨C_K, hC_K_nn, hC_K⟩ := compact_im_bound hK
    by_cases hn : n = 0
    · -- n = 0: integrand is exp(0) = 1, bounded by 1
      subst hn
      exact ⟨fun _ => 1, integrable_const 1, fun z _ => ae_of_all μ fun ω => by
        simp only [Finset.univ_eq_empty, Finset.sum_empty, Complex.exp_zero, norm_one]; rfl⟩
    · -- n > 0: bound by Σᵢ exp(n · C_K · |ω(Jᵢ)|)
      set bound := fun ω : NComponentTorusConfig L_phys params.N =>
        ∑ i : Fin n, Real.exp (↑n * C_K * |ω (J i)|) with hbound_def
      refine ⟨bound, ?_, fun z hz => ae_of_all μ fun ω => ?_⟩
      · -- Integrability of bound: each term exp(n·C_K·|ω(Jᵢ)|) is integrable
        apply integrable_finset_sum; intro i _
        have hscale : ∀ ω : NComponentTorusConfig L_phys params.N,
            Real.exp (↑n * C_K * |ω (J i)|) =
            Real.exp (|ω ((↑n * C_K) • J i)|) := by
          intro ω
          rw [map_smul, smul_eq_mul, abs_mul,
              abs_of_nonneg (mul_nonneg (Nat.cast_nonneg' n) hC_K_nn)]
        simp_rw [hscale]
        exact h_exp ((↑n * C_K) • J i)
      · -- Pointwise bound: ‖F(z, ω)‖ ≤ bound(ω) for z ∈ K
        rw [Complex.norm_exp]
        have h_re : (∑ i : Fin n, Complex.I * z i * ↑(ω (J i))).re =
            -(∑ i : Fin n, (z i).im * ω (J i)) := by
          simp only [Complex.re_sum, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul,
            zero_sub, neg_mul, sub_zero, Finset.sum_neg_distrib]
        rw [h_re]
        calc Real.exp (-(∑ i : Fin n, (z i).im * ω (J i)))
            ≤ Real.exp (|∑ i : Fin n, (z i).im * ω (J i)|) :=
              Real.exp_le_exp_of_le (neg_le_abs _)
          _ ≤ Real.exp (C_K * ∑ i : Fin n, |ω (J i)|) := by
              apply Real.exp_le_exp_of_le
              calc |∑ i, (z i).im * ω (J i)|
                  ≤ ∑ i, |(z i).im * ω (J i)| := Finset.abs_sum_le_sum_abs _ _
                _ = ∑ i, |(z i).im| * |ω (J i)| := by
                    congr 1; ext i; rw [abs_mul]
                _ ≤ ∑ i, C_K * |ω (J i)| :=
                    Finset.sum_le_sum (fun i _ =>
                      mul_le_mul_of_nonneg_right (hC_K z hz i) (abs_nonneg _))
                _ = C_K * ∑ i, |ω (J i)| := (Finset.mul_sum _ _ _).symm
          _ ≤ bound ω := exp_mul_sum_le' (Nat.pos_of_ne_zero hn) C_K hC_K_nn _

/-- **OS1: Regularity of the generating functional.**

‖Z_ℂ[f_re, f_im]‖ ≤ exp(c · (q(f_re) + q(f_im)))
for a continuous seminorm q and constant c > 0.

Proof: from the exponential moment bound, identical to pphi2. -/
theorem lsmTorusLimit_os1 (params : LSMParams)
    (μ : Measure (NComponentTorusConfig L_phys params.N))
    [IsProbabilityMeasure μ]
    (h_exp : ∀ f : NComponentTorusTestFunction L_phys params.N,
      Integrable (fun ω : NComponentTorusConfig L_phys params.N =>
        Real.exp (|ω f|)) μ)
    -- Exponential moment bound: ∫ exp(|ωf|) dμ ≤ K * exp(q(f)²)
    -- for a continuous q and universal K > 0. From Nelson's estimate +
    -- Cauchy-Schwarz density transfer (same as pphi2).
    (h_exp_bound : ∃ (K : ℝ) (q : NComponentTorusTestFunction L_phys params.N → ℝ),
      0 < K ∧ Continuous q ∧
      ∀ f, ∫ ω : NComponentTorusConfig L_phys params.N,
        Real.exp (|ω f|) ∂μ ≤ K * Real.exp (q f ^ 2)) :
    ∃ (q' : NComponentTorusTestFunction L_phys params.N → ℝ) (_ : Continuous q')
      (c : ℝ) (_ : 0 < c),
    ∀ (f_re f_im : NComponentTorusTestFunction L_phys params.N),
      ‖∫ ω : NComponentTorusConfig L_phys params.N,
        Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im))) ∂μ‖ ≤
      Real.exp (c * (q' f_re + q' f_im)) := by
  obtain ⟨K, q, hK, hq_cont, hq_bound⟩ := h_exp_bound
  -- Use q'(f) = q(f)² + |log K| to absorb the constant K
  refine ⟨fun f => q f ^ 2 + |Real.log K|,
          (hq_cont.pow 2).add continuous_const,
          1, one_pos, ?_⟩
  intro f_re f_im
  -- Step 1: Triangle inequality
  have h_tri : ‖∫ ω : NComponentTorusConfig L_phys params.N,
      Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im))) ∂μ‖ ≤
    ∫ ω, ‖Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)))‖ ∂μ :=
    norm_integral_le_integral_norm _
  -- Step 2: ‖exp(I*(ωf_re + I*ωf_im))‖ = exp(-ωf_im)
  have h_norm : ∀ ω : NComponentTorusConfig L_phys params.N,
      ‖Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)))‖ =
      Real.exp (-(ω f_im)) := by
    intro ω
    rw [Complex.norm_exp]; congr 1
    have : Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)) =
        -↑(ω f_im) + ↑(ω f_re) * Complex.I := by
      rw [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul]; ring
    rw [this, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  -- Step 3: Chain the bounds
  have hle_K : K ≤ Real.exp (|Real.log K|) := by
    by_cases h1 : 1 ≤ K
    · rw [abs_of_nonneg (Real.log_nonneg h1), Real.exp_log hK]
    · push Not at h1
      exact le_trans h1.le (Real.one_le_exp (abs_nonneg _))
  calc ‖∫ ω : NComponentTorusConfig L_phys params.N,
          Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im))) ∂μ‖
      ≤ ∫ ω, ‖Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)))‖ ∂μ :=
        h_tri
    _ = ∫ ω, Real.exp (-(ω f_im)) ∂μ := by congr 1; ext ω; exact h_norm ω
    _ ≤ ∫ ω, Real.exp (|ω f_im|) ∂μ := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ (fun _ => (Real.exp_pos _).le)
        · exact h_exp f_im
        · exact ae_of_all _ (fun ω => Real.exp_le_exp_of_le (neg_le_abs (ω f_im)))
    _ ≤ K * Real.exp (q f_im ^ 2) := hq_bound f_im
    _ ≤ Real.exp (|Real.log K|) * Real.exp (q f_im ^ 2) :=
        mul_le_mul_of_nonneg_right hle_K (Real.exp_pos _).le
    _ = Real.exp (q f_im ^ 2 + |Real.log K|) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (1 * ((q f_re ^ 2 + |Real.log K|) + (q f_im ^ 2 + |Real.log K|))) := by
        rw [one_mul]; apply Real.exp_le_exp_of_le
        linarith [sq_nonneg (q f_re), abs_nonneg (Real.log K)]

/-! ## OS2: Translation invariance

The limit measure is invariant under torus translations:
Z[T_v f] = Z[f] for all v ∈ (ℝ/Lℤ)².

**Proof strategy (following pphi2):**

1. **Lattice vector invariance (exact):** For lattice vectors w = (a·j₁, a·j₂)
   where a = L/M, the identity Z_M[T_w f] = Z_M[f] is exact. This follows from
   the interaction's translation invariance (`onInteraction_translation_invariant`)
   combined with GFF measure invariance under site permutations.

2. **Lattice approximation:** For general v ∈ ℝ², approximate v by lattice
   vectors w_n = (a_n · round(v₁/a_n), a_n · round(v₂/a_n)) where a_n → 0
   as the lattice refines. Then w_n → v.

3. **GF Lipschitz:** The generating functional is Lipschitz in the test function:
   |Z_M[T_v f] - Z_M[T_w f]| ≤ B · p(T_v f - T_w f) for a continuous seminorm p,
   uniformly in M.

4. **Error vanishes:** Combining steps 1-3:
   Z_M[T_v f] - Z_M[f] = (Z_M[T_v f] - Z_M[T_{w_n} f]) + 0 → 0

5. **Limit:** Z_∞[T_v f] = lim Z_M[T_v f] = lim Z_M[f] = Z_∞[f]
   by BC convergence + error vanishing + uniqueness of limits. -/

/-- Translation on the N-component test function space.

Translates the torus factor by v ∈ (ℝ/Lℤ)² and leaves the target
ℝ^N factor unchanged:
  T_v(f₁ ⊗ e_i) = (T_v f₁) ⊗ e_i -/
def nComponentTranslation (Nc : ℕ) [NeZero Nc] (v : ℝ × ℝ) :
    NComponentTorusTestFunction L_phys Nc →L[ℝ] NComponentTorusTestFunction L_phys Nc :=
  nuclearTensorProduct_mapCLM
    (torusTranslation L_phys v)
    (ContinuousLinearMap.id ℝ (FinLatticeField 1 Nc))

/-- **Lattice approximation error vanishes along the subsequence.**

For any bounded continuous g : ℝ → ℝ, any v ∈ ℝ², and any test function f,
the difference ∫ g(ω(T_v f)) - g(ω f) dμ_{φ(n)+1} → 0 as n → ∞.

**Proof sketch (following pphi2's `torusGF_latticeApproximation_error_vanishes`):**

For each lattice size M = φ(n)+1 with spacing a = L/M:
1. Choose the nearest lattice vector w_n = (a·round(v₁/a), a·round(v₂/a)).
2. By `onInteraction_translation_invariant` + GFF measure invariance + embedding
   intertwining, ∫ g(ω(T_{w_n} f)) dμ_M = ∫ g(ω f) dμ_M (exact for lattice vectors).
3. So the error = ∫ g(ω(T_v f)) - g(ω(T_{w_n} f)) dμ_M.
4. Since g is bounded continuous and ω(·) is a CLM: g(ω(T_v f)) - g(ω(T_{w_n} f))
   is controlled by |ω(T_v f - T_{w_n} f)| ≤ ‖ω‖ · ‖T_v f - T_{w_n} f‖.
5. As n → ∞: a → 0, so w_n → v, so T_{w_n} f → T_v f by continuity of translation,
   so ‖T_v f - T_{w_n} f‖ → 0, and the error vanishes.

This is the N-component analogue of pphi2's `torusGF_latticeApproximation_error_vanishes`.

Mathematical references:
- Glimm-Jaffe, *Quantum Physics*, §6.1 (lattice translation invariance)
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I (continuum limit construction) -/
axiom lsmGF_latticeApproximation_error_vanishes (params : LSMParams)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (v : ℝ × ℝ) (f : NComponentTorusTestFunction L_phys params.N)
    (g : ℝ → ℝ) (hg : Continuous g) (hg_bdd : ∃ C, ∀ x, |g x| ≤ C) :
    Tendsto (fun n =>
      ∫ ω : NComponentTorusConfig L_phys params.N,
        g (ω (nComponentTranslation L_phys params.N v f))
        ∂(haveI : NeZero (φ n + 1) := ⟨Nat.succ_ne_zero _⟩
          lsmTorusMeasure L_phys params (φ n + 1)) -
      ∫ ω : NComponentTorusConfig L_phys params.N,
        g (ω f)
        ∂(haveI : NeZero (φ n + 1) := ⟨Nat.succ_ne_zero _⟩
          lsmTorusMeasure L_phys params (φ n + 1)))
    atTop (nhds 0)

/-- **OS2: Translation invariance of the generating functional.**

Z[T_v f] = Z[f] for all v ∈ (ℝ/Lℤ)².

Proof (following pphi2's `torusInteractingLimit_translation_invariant`):
- Z_{φ(n)+1}[T_v f] → Z[T_v f] and Z_{φ(n)+1}[f] → Z[f] by weak convergence.
- Their difference Z_{φ(n)+1}[T_v f] - Z_{φ(n)+1}[f] → 0 by the lattice
  approximation error axiom (`lsmGF_latticeApproximation_error_vanishes`).
- By uniqueness of limits: Z[T_v f] = Z[f].

The Re/Im decomposition (cos/sin) is used to pass from ℂ-valued GF to
ℝ-valued BC functions where the error axiom applies. -/
theorem lsmTorusLimit_os2_translation (params : LSMParams)
    (μ : Measure (NComponentTorusConfig L_phys params.N))
    [IsProbabilityMeasure μ]
    -- The limit measure is obtained as a weak limit of lattice measures
    (hμ_conv : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ g : NComponentTorusConfig L_phys params.N → ℝ,
        Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
        Tendsto (fun n => ∫ ω, g ω
          ∂(haveI : NeZero (φ n + 1) := ⟨Nat.succ_ne_zero _⟩
            lsmTorusMeasure L_phys params (φ n + 1)))
          atTop (nhds (∫ ω, g ω ∂μ)))
    (v : ℝ × ℝ) (f : NComponentTorusTestFunction L_phys params.N) :
    ∫ ω : NComponentTorusConfig L_phys params.N,
      Complex.exp (Complex.I * ↑(ω f)) ∂μ =
    ∫ ω : NComponentTorusConfig L_phys params.N,
      Complex.exp (Complex.I * ↑(ω (nComponentTranslation L_phys params.N v f))) ∂μ := by
  obtain ⟨φ, hφ, hconv⟩ := hμ_conv
  set f' := nComponentTranslation L_phys params.N v f
  -- Step 1: BC convergence for cos and sin of f and f' = T_v f
  have hL_cos := hconv (fun ω => Real.cos (ω f))
    (Real.continuous_cos.comp (WeakDual.eval_continuous f))
    ⟨1, fun ω => Real.abs_cos_le_one (ω f)⟩
  have hR_cos := hconv (fun ω => Real.cos (ω f'))
    (Real.continuous_cos.comp (WeakDual.eval_continuous f'))
    ⟨1, fun ω => Real.abs_cos_le_one (ω f')⟩
  have hL_sin := hconv (fun ω => Real.sin (ω f))
    (Real.continuous_sin.comp (WeakDual.eval_continuous f))
    ⟨1, fun ω => Real.abs_sin_le_one (ω f)⟩
  have hR_sin := hconv (fun ω => Real.sin (ω f'))
    (Real.continuous_sin.comp (WeakDual.eval_continuous f'))
    ⟨1, fun ω => Real.abs_sin_le_one (ω f')⟩
  -- Step 2: Lattice approximation error vanishes for cos and sin
  -- ∫ cos(ω(T_v f)) dμ_{φ(n)+1} - ∫ cos(ω f) dμ_{φ(n)+1} → 0
  have h_err_cos := lsmGF_latticeApproximation_error_vanishes L_phys params
    φ hφ v f Real.cos Real.continuous_cos ⟨1, fun x => Real.abs_cos_le_one x⟩
  have h_err_sin := lsmGF_latticeApproximation_error_vanishes L_phys params
    φ hφ v f Real.sin Real.continuous_sin ⟨1, fun x => Real.abs_sin_le_one x⟩
  -- Step 3: By uniqueness of limits.
  -- The difference of limit integrals = limit of differences = 0.
  -- For cos: hR_cos - hL_cos → (∫ cos(ω f') dμ) - (∫ cos(ω f) dμ)
  -- and h_err_cos → 0, so the difference is 0.
  have h_cos_eq : ∫ ω, Real.cos (ω f) ∂μ = ∫ ω, Real.cos (ω f') ∂μ := by
    have h_sub : Tendsto (fun n =>
        ∫ ω, Real.cos (ω f')
          ∂(haveI : NeZero (φ n + 1) := ⟨Nat.succ_ne_zero _⟩
            lsmTorusMeasure L_phys params (φ n + 1)) -
        ∫ ω, Real.cos (ω f)
          ∂(haveI : NeZero (φ n + 1) := ⟨Nat.succ_ne_zero _⟩
            lsmTorusMeasure L_phys params (φ n + 1)))
        atTop (nhds (∫ ω, Real.cos (ω f') ∂μ - ∫ ω, Real.cos (ω f) ∂μ)) :=
      hR_cos.sub hL_cos
    have h_eq : ∫ ω, Real.cos (ω f') ∂μ - ∫ ω, Real.cos (ω f) ∂μ = 0 :=
      tendsto_nhds_unique h_sub h_err_cos
    linarith
  have h_sin_eq : ∫ ω, Real.sin (ω f) ∂μ = ∫ ω, Real.sin (ω f') ∂μ := by
    have h_sub : Tendsto (fun n =>
        ∫ ω, Real.sin (ω f')
          ∂(haveI : NeZero (φ n + 1) := ⟨Nat.succ_ne_zero _⟩
            lsmTorusMeasure L_phys params (φ n + 1)) -
        ∫ ω, Real.sin (ω f)
          ∂(haveI : NeZero (φ n + 1) := ⟨Nat.succ_ne_zero _⟩
            lsmTorusMeasure L_phys params (φ n + 1)))
        atTop (nhds (∫ ω, Real.sin (ω f') ∂μ - ∫ ω, Real.sin (ω f) ∂μ)) :=
      hR_sin.sub hL_sin
    have h_eq : ∫ ω, Real.sin (ω f') ∂μ - ∫ ω, Real.sin (ω f) ∂μ = 0 :=
      tendsto_nhds_unique h_sub h_err_sin
    linarith
  -- Step 4: Reconstruct the complex integral from Re + Im.
  -- ∫ exp(ix) dμ = (∫ cos(x) dμ) + i·(∫ sin(x) dμ) by linearity.
  -- Since Re and Im parts agree, the integrals agree.
  -- Helper: integrability of ω ↦ exp(I * ↑(ω h)) (norm = 1)
  have h_int : ∀ h : NComponentTorusTestFunction L_phys params.N,
      Integrable (fun ω : NComponentTorusConfig L_phys params.N =>
        Complex.exp (Complex.I * ↑(ω h))) μ := fun h =>
    (integrable_const (1 : ℂ)).mono
      ((Complex.measurable_exp.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp
          (configuration_eval_measurable h)))).aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        simp only [norm_one]
        rw [show Complex.I * ↑(ω h) = ↑(ω h) * Complex.I from mul_comm _ _]
        exact le_of_eq (Complex.norm_exp_ofReal_mul_I (ω h)))
  -- Helper: re of ∫ exp(I * ω h) = ∫ cos(ω h)
  have h_re : ∀ h : NComponentTorusTestFunction L_phys params.N,
      (∫ ω, Complex.exp (Complex.I * ↑(ω h)) ∂μ).re =
      ∫ ω : NComponentTorusConfig L_phys params.N, Real.cos (ω h) ∂μ := fun h => by
    rw [show (∫ ω, Complex.exp (Complex.I * ↑(ω h)) ∂μ).re =
      Complex.reCLM (∫ ω, Complex.exp (Complex.I * ↑(ω h)) ∂μ) from rfl]
    rw [← ContinuousLinearMap.integral_comp_comm Complex.reCLM (h_int h)]
    congr 1 with ω
    simp only [Complex.reCLM_apply, mul_comm Complex.I, Complex.exp_mul_I,
      Complex.add_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.sin_ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    exact Complex.cos_ofReal_re (ω h)
  -- Helper: im of ∫ exp(I * ω h) = ∫ sin(ω h)
  have h_im : ∀ h : NComponentTorusTestFunction L_phys params.N,
      (∫ ω, Complex.exp (Complex.I * ↑(ω h)) ∂μ).im =
      ∫ ω : NComponentTorusConfig L_phys params.N, Real.sin (ω h) ∂μ := fun h => by
    rw [show (∫ ω, Complex.exp (Complex.I * ↑(ω h)) ∂μ).im =
      Complex.imCLM (∫ ω, Complex.exp (Complex.I * ↑(ω h)) ∂μ) from rfl]
    rw [← ContinuousLinearMap.integral_comp_comm Complex.imCLM (h_int h)]
    congr 1 with ω
    simp only [Complex.imCLM_apply, mul_comm Complex.I, Complex.exp_mul_I,
      Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
    ring
  apply Complex.ext
  · -- Re parts: ∫ exp(iωf) re = ∫ cos(ωf) = ∫ cos(ωf') = ∫ exp(iωf') re
    rw [h_re f, h_re f']
    exact h_cos_eq
  · -- Im parts: ∫ exp(iωf) im = ∫ sin(ωf) = ∫ sin(ωf') = ∫ exp(iωf') im
    rw [h_im f, h_im f']
    exact h_sin_eq

/-! ## Uniform exponential moment bound (lattice level)

The key analytic input: exp(|ω f|) has a uniform bound over all lattice
sizes M. This follows from:
1. Density transfer (lsmDensityTransferConstant):
   ∫ F dμ_int ≤ D * ∫ F dμ_GFF  (for nonneg F, uniformly in M)
2. GFF exponential moment (Gaussian MGF):
   ∫ exp(|embed φ f|) dμ_N ≤ 2 exp(σ²(f)/2) where σ²(f) = ∫(embed φ f)² dμ_N
3. GFF second moment uniform bound (nComponentGreen_uniform_bound):
   σ²(f) ≤ C * q(f)² for continuous q (uniform in M)
Combined: ∫ exp(|ωf|) dμ_int ≤ 2D * exp(C*q(f)²/2). -/

/-- **Uniform Gaussian exponential moment bound (textbook axiom).**

For the N-component GFF pushed forward to the continuum:
  ∫ exp(|ω f|) d(map embed μ_N) ≤ K_exp * exp(q_exp(f)²)

with K_exp > 0 and q_exp continuous, both independent of M.

Proof chain:
1. (embed φ)(f) is Gaussian under the N-component GFF with variance
   σ²(f) = G(f,f) (Green's function bilinear form)
2. Gaussian MGF: E[exp(|X|)] ≤ 2 exp(σ²/2) for X ~ N(0,σ²)
   (use E[exp(|X|)] ≤ E[exp(X)] + E[exp(-X)] = 2 exp(σ²/2))
3. σ²(f) ≤ C * q(f)² uniformly in M (from nComponentGreen_uniform_bound)
4. Combined: K_exp = 2, q_exp = sqrt(C/2) * q_gff -/
axiom nComponentGFF_exp_moment_uniform (Nc : ℕ) [NeZero Nc]
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (K_exp : ℝ) (q_exp : NComponentTorusTestFunction L_phys Nc → ℝ),
      0 < K_exp ∧ Continuous q_exp ∧
      ∀ (M : ℕ) [NeZero M] (f : NComponentTorusTestFunction L_phys Nc),
        Integrable (fun ω : NComponentTorusConfig L_phys Nc =>
          Real.exp (|ω f|))
          (Measure.map (nComponentTorusEmbedLift L_phys Nc M)
            (nComponentMeasure Nc
              (scalarLatticeGFF mass (L_phys / M)
                (div_pos hL.out (Nat.cast_pos.mpr (NeZero.pos M))) hmass M))) ∧
        ∫ ω : NComponentTorusConfig L_phys Nc,
          Real.exp (|ω f|)
          ∂(Measure.map (nComponentTorusEmbedLift L_phys Nc M)
            (nComponentMeasure Nc
              (scalarLatticeGFF mass (L_phys / M)
                (div_pos hL.out (Nat.cast_pos.mpr (NeZero.pos M))) hmass M))) ≤
          K_exp * Real.exp (q_exp f ^ 2)

/-- Uniform exponential moment bound for the LSM torus measures.

For each test function f and all lattice sizes M ≥ 1:
  ∫ exp(|ω f|) d(lsmTorusMeasure M) ≤ K * exp(q(f)²)

where K > 0 and q is a continuous seminorm, both independent of M.

Proof: density transfer + GFF exponential moment bound. -/
private theorem lsmTorus_exp_moment_uniform (params : LSMParams) :
    ∃ (K : ℝ) (q : NComponentTorusTestFunction L_phys params.N → ℝ),
      0 < K ∧ Continuous q ∧
      ∀ (M : ℕ) [NeZero M] (f : NComponentTorusTestFunction L_phys params.N),
        Integrable (fun ω : NComponentTorusConfig L_phys params.N =>
          Real.exp (|ω f|)) (lsmTorusMeasure L_phys params M) ∧
        ∫ ω : NComponentTorusConfig L_phys params.N,
          Real.exp (|ω f|) ∂(lsmTorusMeasure L_phys params M) ≤
          K * Real.exp (q f ^ 2) := by
  -- Get GFF exponential moment bound
  obtain ⟨K_exp, q_exp, hK_exp, hq_exp_cont, h_gff_exp⟩ :=
    nComponentGFF_exp_moment_uniform L_phys params.N params.mass params.hmass
  -- Get density transfer constant
  obtain ⟨D, hD_pos, h_density⟩ := lsmDensityTransferConstant L_phys params
  -- Combined: K = D * K_exp, q = q_exp
  refine ⟨D * K_exp, q_exp, mul_pos hD_pos hK_exp, hq_exp_cont, fun M _ f => ?_⟩
  -- Abbreviations
  set sp := L_phys / (M : ℝ)
  have hsp : 0 < sp := div_pos hL.out (Nat.cast_pos.mpr (NeZero.pos M))
  set μ_sc := scalarLatticeGFF params.mass sp hsp params.hmass M
  set μ_N := nComponentMeasure params.N μ_sc
  set embed := nComponentTorusEmbedLift L_phys params.N M
  have hembed_meas : Measurable embed := nComponentTorusEmbedLift_measurable L_phys params.N M
  -- F(ω) = exp(|ω f|) is measurable
  have hF_meas : Measurable (fun ω : NComponentTorusConfig L_phys params.N =>
      Real.exp (|ω f|)) :=
    Real.measurable_exp.comp (measurable_abs.comp (configuration_eval_measurable f))
  -- GFF exponential moment: integrability + bound
  obtain ⟨h_gff_int, h_gff_bound⟩ := h_gff_exp M f
  -- Pull through the embedding map
  -- lsmTorusMeasure = map embed (onInteractingMeasure ...)
  -- First establish: ∫ exp(|ωf|) d(lsmTorusMeasure) = ∫ exp(|embed(φ)(f)|) d(onInteracting)
  have h_map_lsm : ∫ ω, Real.exp (|ω f|) ∂(lsmTorusMeasure L_phys params M) =
      ∫ φ, Real.exp (|embed φ f|) ∂(onInteractingMeasure params.N 2 M
        params.toONModel.interaction
        (latticeWickConstant sp params.mass hsp params.hmass M) sp μ_sc) := by
    show ∫ ω, Real.exp (|ω f|) ∂(Measure.map embed
      (onInteractingMeasure params.N 2 M params.toONModel.interaction
        (latticeWickConstant sp params.mass hsp params.hmass M) sp μ_sc)) = _
    rw [integral_map hembed_meas.aemeasurable hF_meas.aestronglyMeasurable]
  -- GFF version: ∫ exp(|ωf|) d(map embed μ_N) = ∫ exp(|embed(φ)(f)|) dμ_N
  have h_map_gff : ∫ ω, Real.exp (|ω f|) ∂(Measure.map embed μ_N) =
      ∫ φ, Real.exp (|embed φ f|) ∂μ_N := by
    rw [integral_map hembed_meas.aemeasurable hF_meas.aestronglyMeasurable]
  -- GFF integrability of exp(|embed(φ)(f)|) under μ_N
  have hF_int_gff : Integrable (fun φ => Real.exp (|embed φ f|)) μ_N := by
    show Integrable ((fun ω : NComponentTorusConfig L_phys params.N =>
      Real.exp (|ω f|)) ∘ embed) μ_N
    exact (integrable_map_measure hF_meas.aestronglyMeasurable
      hembed_meas.aemeasurable).mp h_gff_int
  -- Density transfer: integrability + integral bound
  obtain ⟨h_int_interacting, h_dt⟩ :=
    h_density M _ (fun φ => (Real.exp_pos _).le) (hF_meas.comp hembed_meas) hF_int_gff
  -- GFF bound: ∫ exp(|embed(φ)(f)|) dμ_N ≤ K_exp * exp(q_exp(f)²)
  have h_gff_rw : ∫ φ, Real.exp (|embed φ f|) ∂μ_N =
      ∫ ω, Real.exp (|ω f|) ∂(Measure.map embed μ_N) := h_map_gff.symm
  constructor
  · -- Integrability under lsmTorusMeasure = map embed (interacting)
    show Integrable (fun ω => Real.exp (|ω f|))
      (Measure.map embed (onInteractingMeasure params.N 2 M
        params.toONModel.interaction
        (latticeWickConstant sp params.mass hsp params.hmass M) sp μ_sc))
    exact (integrable_map_measure hF_meas.aestronglyMeasurable
      hembed_meas.aemeasurable).mpr h_int_interacting
  · -- Integral bound
    calc ∫ ω, Real.exp (|ω f|) ∂(lsmTorusMeasure L_phys params M)
        = ∫ φ, Real.exp (|embed φ f|) ∂(onInteractingMeasure params.N 2 M
            params.toONModel.interaction
            (latticeWickConstant sp params.mass hsp params.hmass M) sp μ_sc) :=
          h_map_lsm
      _ ≤ D * ∫ φ, Real.exp (|embed φ f|) ∂μ_N := h_dt
      _ = D * ∫ ω, Real.exp (|ω f|) ∂(Measure.map embed μ_N) := by rw [h_map_gff]
      _ ≤ D * (K_exp * Real.exp (q_exp f ^ 2)) :=
          mul_le_mul_of_nonneg_left h_gff_bound hD_pos.le
      _ = D * K_exp * Real.exp (q_exp f ^ 2) := by ring

/-- Exponential moments pass from lattice measures to the weak limit.

If ∀ n, ∫ exp(|ω f|) dμ_n ≤ B (uniform bound) and μ_n → μ in BC sense,
then ∫ exp(|ω f|) dμ ≤ B (via truncation + MCT).

This is a generic result for any `Configuration E` space, proved by:
1. Bounding truncations min(exp(|ω f|), M+1) ≤ B using BC convergence
2. MCT: sup over truncations = full integral -/
private theorem limit_exp_moment_from_bc
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DyninMityaginSpace E]
    (νseq : ℕ → Measure (Configuration E))
    (ν : Measure (Configuration E))
    [IsProbabilityMeasure ν]
    (hbc : ∀ (g : Configuration E → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Tendsto (fun n => ∫ ω, g ω ∂(νseq n)) atTop (nhds (∫ ω, g ω ∂ν)))
    (f : E) (B : ℝ)
    (h_unif : ∀ n,
      Integrable (fun ω => Real.exp (|ω f|)) (νseq n) ∧
      ∫ ω, Real.exp (|ω f|) ∂(νseq n) ≤ B) :
    Integrable (fun ω => Real.exp (|ω f|)) ν ∧
    ∫ ω, Real.exp (|ω f|) ∂ν ≤ B := by
  -- Abbreviate: F ω = exp(|ω f|)
  set F : Configuration E → ℝ := fun ω => Real.exp (|ω f|) with hF_def
  have hF_nn : ∀ ω : Configuration E, 0 ≤ F ω :=
    fun ω => (Real.exp_pos _).le
  -- ω ↦ ω f is continuous (WeakDual evaluation)
  have heval_cont : Continuous (fun ω : Configuration E => ω f) :=
    WeakDual.eval_continuous f
  -- ω ↦ ω f is measurable (for ae arguments)
  have heval_meas : Measurable (fun ω : Configuration E => ω f) :=
    configuration_eval_measurable f
  -- F is ae strongly measurable under ν
  have hF_meas : AEStronglyMeasurable F ν :=
    (Real.continuous_exp.comp continuous_abs).comp_aestronglyMeasurable
      heval_meas.aestronglyMeasurable
  -- Truncations: gM ω = min(F ω, M+1) are bounded and continuous
  have hgM_nn : ∀ (M : ℕ) (ω : Configuration E),
      0 ≤ min (F ω) (↑(M + 1) : ℝ) :=
    fun M ω => le_min (Real.exp_pos _).le (by positivity)
  -- Step 1: For each M, ∫ min(F, M+1) dν ≤ B
  have hgM_int_le : ∀ M : ℕ, ∫ ω, min (F ω) (↑(M + 1) : ℝ) ∂ν ≤ B := by
    intro M
    have hgM_cont : Continuous (fun ω : Configuration E =>
        min (F ω) (↑(M + 1) : ℝ)) :=
      (Real.continuous_exp.comp (continuous_abs.comp heval_cont)).min continuous_const
    have hgM_bound : ∃ C : ℝ, ∀ ω : Configuration E,
        |min (F ω) (↑(M + 1) : ℝ)| ≤ C :=
      ⟨↑(M + 1), fun ω => by
        rw [abs_of_nonneg (hgM_nn M ω)]; exact min_le_right _ _⟩
    have hbc_gM := hbc _ hgM_cont hgM_bound
    -- Each ∫ min(F, M+1) dνseq_n ≤ B
    have h_each_le : ∀ n, ∫ ω, min (F ω) (↑(M + 1) : ℝ) ∂(νseq n) ≤ B :=
      fun n => (integral_mono_of_nonneg (ae_of_all _ (hgM_nn M)) (h_unif n).1
        (ae_of_all _ (fun ω => min_le_left _ _))).trans (h_unif n).2
    exact le_of_tendsto hbc_gM (Eventually.of_forall h_each_le)
  -- Step 2: MCT via ENNReal lintegral
  have hgMenr_meas : ∀ M : ℕ, Measurable (fun ω : Configuration E =>
      ENNReal.ofReal (min (F ω) (↑(M + 1) : ℝ))) :=
    fun M => ENNReal.measurable_ofReal.comp
      ((Real.measurable_exp.comp
        (measurable_abs.comp heval_meas)).min measurable_const)
  have hgMenr_mono : Monotone (fun (M : ℕ) (ω : Configuration E) =>
      ENNReal.ofReal (min (F ω) (↑(M + 1) : ℝ))) :=
    fun m n hmn ω => ENNReal.ofReal_le_ofReal
      (min_le_min_left _ (by exact_mod_cast Nat.add_le_add_right hmn 1))
  -- Pointwise iSup = F
  have hgMenr_iSup : ∀ ω : Configuration E,
      ⨆ M : ℕ, ENNReal.ofReal (min (F ω) (↑(M + 1) : ℝ)) =
      ENNReal.ofReal (F ω) := by
    intro ω
    apply le_antisymm
    · exact iSup_le fun M => ENNReal.ofReal_le_ofReal (min_le_left _ _)
    · apply le_iSup_of_le (Nat.ceil (F ω))
      apply ENNReal.ofReal_le_ofReal
      apply le_min le_rfl
      linarith [Nat.le_ceil (F ω),
        show (⌈F ω⌉₊ : ℝ) ≤ ↑(⌈F ω⌉₊ + 1) from by push_cast; linarith]
  -- MCT: ∫⁻ F dν = sup_M ∫⁻ min(F, M+1) dν
  have hlint_iSup : ∫⁻ ω, ENNReal.ofReal (F ω) ∂ν =
      ⨆ (M : ℕ), ∫⁻ ω, ENNReal.ofReal (min (F ω) (↑(M + 1) : ℝ)) ∂ν := by
    conv_lhs => rw [show (fun ω : Configuration E => ENNReal.ofReal (F ω)) =
      fun ω => ⨆ M : ℕ, ENNReal.ofReal (min (F ω) (↑(M + 1) : ℝ)) from
      funext fun ω => (hgMenr_iSup ω).symm]
    rw [lintegral_iSup hgMenr_meas hgMenr_mono]
  -- Each ∫⁻ min(F, M+1) dν ≤ ENNReal.ofReal B
  have hB_nn : 0 ≤ B :=
    le_trans (integral_nonneg (fun ω => hF_nn ω)) (h_unif 0).2
  have hlint_gM_le : ∀ M : ℕ,
      ∫⁻ ω, ENNReal.ofReal (min (F ω) (↑(M + 1) : ℝ)) ∂ν ≤ ENNReal.ofReal B := by
    intro M
    have hgM_ae : AEStronglyMeasurable
        (fun ω : Configuration E => min (F ω) (↑(M + 1) : ℝ)) ν :=
      ((Real.continuous_exp.comp continuous_abs).min continuous_const)
        |>.comp_aestronglyMeasurable heval_meas.aestronglyMeasurable
    have hgM_int : Integrable (fun ω => min (F ω) (↑(M + 1) : ℝ)) ν :=
      Integrable.of_bound hgM_ae (↑(M + 1) : ℝ) (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (hgM_nn M ω)]; exact min_le_right _ _)
    rw [← ofReal_integral_eq_lintegral_ofReal hgM_int (ae_of_all _ (hgM_nn M))]
    exact ENNReal.ofReal_le_ofReal (hgM_int_le M)
  have hlint_le : ∫⁻ ω, ENNReal.ofReal (F ω) ∂ν ≤ ENNReal.ofReal B :=
    hlint_iSup ▸ iSup_le (fun M => hlint_gM_le M)
  -- Step 3a: Integrability from finite lintegral
  have hint : Integrable F ν := by
    rw [← lintegral_ofReal_ne_top_iff_integrable hF_meas (ae_of_all _ hF_nn)]
    exact (hlint_le.trans_lt ENNReal.ofReal_lt_top).ne
  -- Step 3b: ∫ F dν ≤ B
  constructor
  · exact hint
  · have heq := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hF_nn)
    rw [← heq] at hlint_le
    exact (ENNReal.ofReal_le_ofReal_iff hB_nn).mp hlint_le

/-! ## Bundled OS structure -/

/-- **The O(N) torus continuum limit satisfies OS0-OS2.**

This bundles the existence of the limit with the OS axioms,
analogous to pphi2's `torusInteracting_satisfies_OS`. -/
theorem lsmTorusLimit_satisfies_OS (params : LSMParams) :
    ∃ (μ : Measure (NComponentTorusConfig L_phys params.N)),
      IsProbabilityMeasure μ ∧
      -- OS0: analyticity
      (∀ (n : ℕ) (J : Fin n → NComponentTorusTestFunction L_phys params.N),
        AnalyticOnNhd ℂ (fun z : Fin n → ℂ =>
          ∫ ω, Complex.exp (∑ i, Complex.I * z i * ↑(ω (J i))) ∂μ) Set.univ) ∧
      -- OS1: regularity
      (∃ (q : NComponentTorusTestFunction L_phys params.N → ℝ) (_ : Continuous q)
        (c : ℝ) (_ : 0 < c),
        ∀ (f_re f_im : NComponentTorusTestFunction L_phys params.N),
          ‖∫ ω, Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im))) ∂μ‖ ≤
          Real.exp (c * (q f_re + q f_im))) ∧
      -- OS2: translation invariance
      (∀ (v : ℝ × ℝ) (f : NComponentTorusTestFunction L_phys params.N),
        ∫ ω : NComponentTorusConfig L_phys params.N,
          Complex.exp (Complex.I * ↑(ω f)) ∂μ =
        ∫ ω, Complex.exp (Complex.I *
          ↑(ω (nComponentTranslation L_phys params.N v f))) ∂μ) := by
  obtain ⟨μ, hμ_prob, φ, hφ_mono, hμ_conv⟩ := lsmTorusLimit_exists L_phys params
  haveI := hμ_prob
  -- Get uniform exp moment bound for all lattice measures
  obtain ⟨K, q, hK_pos, hq_cont, h_unif_bound⟩ :=
    lsmTorus_exp_moment_uniform L_phys params
  -- The subsequence measures νseq n = lsmTorusMeasure (φ n + 1)
  set νseq : ℕ → Measure (NComponentTorusConfig L_phys params.N) :=
    fun n => haveI : NeZero (φ n + 1) := ⟨Nat.succ_ne_zero _⟩
      lsmTorusMeasure L_phys params (φ n + 1) with hνseq_def
  -- h_exp: exp(|ω f|) is integrable under μ, for each f
  have h_exp : ∀ f, Integrable (fun ω : NComponentTorusConfig L_phys params.N =>
      Real.exp (|ω f|)) μ := by
    intro f
    -- Apply limit_exp_moment_from_bc with B = K * exp(q(f)^2)
    set B := K * Real.exp (q f ^ 2) with hB_def
    have h_unif_f : ∀ n,
        Integrable (fun ω => Real.exp (|ω f|)) (νseq n) ∧
        ∫ ω, Real.exp (|ω f|) ∂(νseq n) ≤ B := by
      intro n
      simp only [νseq]
      haveI : NeZero (φ n + 1) := ⟨Nat.succ_ne_zero _⟩
      exact h_unif_bound (φ n + 1) f
    exact (limit_exp_moment_from_bc νseq μ
      (fun g hg hbdd => hμ_conv g hg hbdd) f B h_unif_f).1
  -- h_exp_bound: explicit exponential moment bound for μ
  have h_exp_bound : ∃ (K' : ℝ) (q' : NComponentTorusTestFunction L_phys params.N → ℝ),
      0 < K' ∧ Continuous q' ∧
      ∀ f, ∫ ω : NComponentTorusConfig L_phys params.N,
        Real.exp (|ω f|) ∂μ ≤ K' * Real.exp (q' f ^ 2) := by
    -- Use the same K and q from lsmTorus_exp_moment_uniform, applied via BC limit
    refine ⟨K, q, hK_pos, hq_cont, fun f => ?_⟩
    set B := K * Real.exp (q f ^ 2) with hB_def
    have h_unif_f : ∀ n,
        Integrable (fun ω => Real.exp (|ω f|)) (νseq n) ∧
        ∫ ω, Real.exp (|ω f|) ∂(νseq n) ≤ B := by
      intro n
      simp only [νseq]
      haveI : NeZero (φ n + 1) := ⟨Nat.succ_ne_zero _⟩
      exact h_unif_bound (φ n + 1) f
    exact (limit_exp_moment_from_bc νseq μ
      (fun g hg hbdd => hμ_conv g hg hbdd) f B h_unif_f).2
  refine ⟨μ, hμ_prob, ?_, ?_, ?_⟩
  · exact fun n J => lsmTorusLimit_os0 L_phys params μ h_exp n J
  · exact lsmTorusLimit_os1 L_phys params μ h_exp h_exp_bound
  · -- OS2: translation invariance via BC convergence
    intro v f
    exact lsmTorusLimit_os2_translation L_phys params μ ⟨φ, hφ_mono, hμ_conv⟩ v f

end Pphi2N

end
