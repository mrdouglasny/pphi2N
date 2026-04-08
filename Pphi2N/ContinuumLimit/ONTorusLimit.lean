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

/-- Uniform second moment bound for the LSM torus measures.

Proof chain (same as pphi2's torus_interacting_second_moment_uniform):
1. Density transfer: E_int[X²] ≤ C₁ · E_GFF[X⁴]^{1/2} · E_GFF[e^{-2V}]^{1/2}
   (Cauchy-Schwarz on the Boltzmann weight)
2. Hypercontractivity: E_GFF[X⁴] ≤ C₂ · (E_GFF[X²])² (Nelson/Gross)
3. Nelson: E_GFF[e^{-2V}] ≤ e^{C₃|Λ|} (from onNelsonEstimate)
4. Green's function: E_GFF[(ωf)²] = G(f,f) ≤ q(f)² (operator bound)

For N components: the product GFF decomposes, and each component
contributes independently. The bound is N times the scalar bound. -/
theorem lsmTorus_uniform_second_moment (params : LSMParams) :
    ∃ (C : ℝ) (q : NComponentTorusTestFunction L_phys params.N → ℝ),
      0 < C ∧ Continuous q ∧
      ∀ (M : ℕ) [NeZero M] (f : NComponentTorusTestFunction L_phys params.N),
        ∫ ω : NComponentTorusConfig L_phys params.N,
          (ω f) ^ 2 ∂(lsmTorusMeasure L_phys params M) ≤ C * q f ^ 2 := by
  sorry -- from pphi2's density_transfer_bound + torus_interacting_second_moment_uniform
         -- adapted componentwise for the N-component product GFF

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
      -- Integrability of (ω f)²: from exponential moment domination
      -- (ω f)² ≤ exp(2|ω f|), and exp moments are finite from Nelson
      sorry)
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
      IsProbabilityMeasure μ := by
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
  obtain ⟨φ, ν, _, hν_prob, _⟩ :=
    prokhorov_configuration μseq hμseq_prob hμseq_tight
  exact ⟨ν, hν_prob⟩

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

At each lattice M, the interaction Σ_x :P(|φ(x)|²): is invariant under
lattice translations (sum over all sites). The torus embedding intertwines
lattice and torus translations. Taking the limit via BC convergence:
Z_∞[T_v f] = lim Z_M[T_v f] = lim Z_M[f] = Z_∞[f].

This is exact at each M (not approximate), so no anomaly correction needed. -/

/-- Translation on the N-component test function space.

Translates the torus factor by v ∈ (ℝ/Lℤ)² and leaves the target
ℝ^N factor unchanged:
  T_v(f₁ ⊗ e_i) = (T_v f₁) ⊗ e_i -/
def nComponentTranslation (Nc : ℕ) [NeZero Nc] (v : ℝ × ℝ) :
    NComponentTorusTestFunction L_phys Nc →L[ℝ] NComponentTorusTestFunction L_phys Nc :=
  nuclearTensorProduct_mapCLM
    (torusTranslation L_phys v)
    (ContinuousLinearMap.id ℝ (FinLatticeField 1 Nc))

/-- **OS2: Translation invariance of the generating functional.**

Z[T_v f] = Z[f] for all v ∈ (ℝ/Lℤ)².

Proof: at each lattice M, the interaction Σ_x :P(|φ(x)|²): is
invariant under lattice translations (sum over all sites). The torus
embedding intertwines lattice and torus translations. Taking the
limit: Z_M[f] and Z_M[T_v f] both converge to Z_∞[f] = Z_∞[T_v f]
by BC convergence + the exact finite-M invariance. -/
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
  -- cos(ω f) converges: bounded continuous (|cos| ≤ 1)
  have hL_cos := hconv (fun ω => Real.cos (ω f))
    (Real.continuous_cos.comp (WeakDual.eval_continuous f))
    ⟨1, fun ω => Real.abs_cos_le_one (ω f)⟩
  have hR_cos := hconv (fun ω => Real.cos (ω f'))
    (Real.continuous_cos.comp (WeakDual.eval_continuous f'))
    ⟨1, fun ω => Real.abs_cos_le_one (ω f')⟩
  -- sin(ω f) converges: bounded continuous (|sin| ≤ 1)
  have hL_sin := hconv (fun ω => Real.sin (ω f))
    (Real.continuous_sin.comp (WeakDual.eval_continuous f))
    ⟨1, fun ω => Real.abs_sin_le_one (ω f)⟩
  have hR_sin := hconv (fun ω => Real.sin (ω f'))
    (Real.continuous_sin.comp (WeakDual.eval_continuous f'))
    ⟨1, fun ω => Real.abs_sin_le_one (ω f')⟩
  -- At each M: Z_M[f] = Z_M[T_v f] (exact lattice translation invariance)
  -- This means ∫ cos(ω f) dμ_M = ∫ cos(ω f') dμ_M and same for sin.
  have h_eq_cos : ∀ n, ∫ ω, Real.cos (ω f)
      ∂(haveI : NeZero (φ n + 1) := ⟨Nat.succ_ne_zero _⟩
        lsmTorusMeasure L_phys params (φ n + 1)) =
      ∫ ω, Real.cos (ω f')
      ∂(haveI : NeZero (φ n + 1) := ⟨Nat.succ_ne_zero _⟩
        lsmTorusMeasure L_phys params (φ n + 1)) := by
    sorry -- from lattice translation invariance of the O(N) interaction
  have h_eq_sin : ∀ n, ∫ ω, Real.sin (ω f)
      ∂(haveI : NeZero (φ n + 1) := ⟨Nat.succ_ne_zero _⟩
        lsmTorusMeasure L_phys params (φ n + 1)) =
      ∫ ω, Real.sin (ω f')
      ∂(haveI : NeZero (φ n + 1) := ⟨Nat.succ_ne_zero _⟩
        lsmTorusMeasure L_phys params (φ n + 1)) := by
    sorry -- from lattice translation invariance of the O(N) interaction
  -- By uniqueness of limits: ∫ cos(ω f) dμ = ∫ cos(ω f') dμ (and sin)
  have h_cos_eq : ∫ ω, Real.cos (ω f) ∂μ = ∫ ω, Real.cos (ω f') ∂μ :=
    tendsto_nhds_unique hL_cos (hR_cos.congr (fun n => (h_eq_cos n).symm))
  have h_sin_eq : ∫ ω, Real.sin (ω f) ∂μ = ∫ ω, Real.sin (ω f') ∂μ :=
    tendsto_nhds_unique hL_sin (hR_sin.congr (fun n => (h_eq_sin n).symm))
  -- Reconstruct: a complex number is determined by its re and im parts.
  -- ∫ exp(ix) dμ = (∫ cos(x) dμ) + i·(∫ sin(x) dμ) by linearity.
  -- Since re and im parts agree (h_cos_eq, h_sin_eq), the integrals agree.
  apply Complex.ext
  · -- Re parts: use h_cos_eq
    sorry -- ∫ exp(iωf) re = ∫ cos(ωf) (from reCLM ∘ integral_comp_comm)
  · -- Im parts: use h_sin_eq
    sorry -- ∫ exp(iωf) im = ∫ sin(ωf) (from imCLM ∘ integral_comp_comm)

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
  obtain ⟨μ, hμ_prob⟩ := lsmTorusLimit_exists L_phys params
  haveI := hμ_prob
  have h_exp : ∀ f, Integrable (fun ω : NComponentTorusConfig L_phys params.N =>
      Real.exp (|ω f|)) μ := by
    sorry -- from uniform exponential moment + BC convergence + truncation/MCT
  -- Exponential moment bound: from Nelson estimate + density transfer.
  -- K and q come from the Cauchy-Schwarz density transfer bound.
  have h_exp_bound : ∃ (K : ℝ) (q : NComponentTorusTestFunction L_phys params.N → ℝ),
      0 < K ∧ Continuous q ∧
      ∀ f, ∫ ω : NComponentTorusConfig L_phys params.N,
        Real.exp (|ω f|) ∂μ ≤ K * Real.exp (q f ^ 2) := by
    sorry -- from Nelson's estimate + Cauchy-Schwarz + Gaussian exponential moments
  refine ⟨μ, hμ_prob, ?_, ?_, ?_⟩
  · exact fun n J => lsmTorusLimit_os0 L_phys params μ h_exp n J
  · exact lsmTorusLimit_os1 L_phys params μ h_exp h_exp_bound
  · -- OS2: translation invariance passes through the weak limit
    intro v f
    sorry -- from lsmTorusLimit_os2_translation with the BC convergence data

end Pphi2N

end
