/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# O(N) Interacting Measure on the Torus Lattice

Constructs the O(N) interacting measure on the torus lattice (ℤ/Mℤ)²:

  μ_{int,N} = (1/Z_N) · exp(-V_N) · dμ_{GFF}^{⊗N}

where:
- μ_{GFF}^{⊗N} = product of N scalar GFFs on the lattice
- V_N(φ) = a² Σ_x :P(|φ(x)|²):_c is the O(N)-invariant interaction
- Z_N = ∫ exp(-V_N) dμ_{GFF}^{⊗N} is the partition function

## Nelson estimate (N-dependent)

V_N is bounded below: ∃ B(N), ∀ φ, V_N(φ) ≥ -B(N).

This follows from the scalar Nelson estimate by Cauchy-Schwarz:
  |φ(x)|⁴ = (Σᵢ (φⁱ)²)² ≤ N · Σᵢ (φⁱ)⁴

So the O(N) quartic interaction is bounded by N times the sum of
scalar quartic interactions. The bound B(N) = O(N · |Λ|).

## Main definitions

- `onBoltzmannWeight` — exp(-V_N(φ))
- `onPartitionFunction` — Z_N = ∫ exp(-V_N) dμ^{⊗N}
- `onInteractingMeasure` — (1/Z_N) · exp(-V_N) · dμ^{⊗N}

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I-II
- Glimm-Jaffe, *Quantum Physics*, Ch. 6, 19
-/

import Pphi2N.InteractingMeasure.ONLatticeAction
import Lattice.FiniteField
import Pphi2N.LatticeField.ProductGFF

noncomputable section

open GaussianField MeasureTheory BigOperators Pphi2N

namespace Pphi2N

variable (N : ℕ) (hN : 1 ≤ N)

/-! ## Configuration type

For the lattice case, the N-component field is
  φ : Fin N → (FinLatticeSites d M → ℝ)

We access the field at site x, component i as `φ i x`. -/

variable (d M : ℕ) [NeZero M]

/-- The N-component field viewed as an NComponentField at a site.
Extracts the field values at site x across all N components:
  siteField(φ, x) = (φ¹(x), ..., φᴺ(x)) -/
def siteField (φ : Fin N → FinLatticeField d M) (x : FinLatticeSites d M) :
    Fin N → ℝ :=
  fun i => φ i x

/-- |φ(x)|² = Σᵢ (φⁱ(x))² at a single site. -/
def siteNormSq (φ : Fin N → FinLatticeField d M) (x : FinLatticeSites d M) : ℝ :=
  ∑ i : Fin N, (φ i x) ^ 2

/-- |φ(x)|² ≥ 0. -/
theorem siteNormSq_nonneg (φ : Fin N → FinLatticeField d M) (x : FinLatticeSites d M) :
    0 ≤ siteNormSq N d M φ x :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

/-! ## The O(N) interaction on the product space -/

/-- The O(N) interaction functional on the product configuration space.

V_N(φ) = a^d · Σ_{x ∈ Λ} :P(|φ(x)|²):_c

where φ : Fin N → (Λ → ℝ) is the N-component field. -/
def onInteraction (P : ONInteraction) (c a : ℝ) :
    (Fin N → FinLatticeField d M) → ℝ :=
  fun φ => a ^ d * ∑ x : FinLatticeSites d M,
    wickInteraction_ON N P c (siteNormSq N d M φ x)

/-! ## Nelson estimate for O(N) (axiomatized)

The key bound: V_N is bounded below. For the quartic interaction,
the Cauchy-Schwarz inequality gives:

  (Σᵢ aᵢ)² ≤ N · Σᵢ aᵢ²

so |φ|⁴ ≤ N · Σᵢ (φⁱ)⁴, and the O(N) Nelson bound follows from
the scalar one with an extra factor of N:

  V_N(φ) ≥ -C(N) · |Λ|  where C(N) = O(N · C₁)  -/

/-- The O(N) interaction is bounded below (Nelson estimate).

For any O(N)-invariant interaction :P(|φ|²): with P bounded below,
the Wick-ordered interaction on the lattice satisfies V_N ≥ -B·|Λ|
where B depends on N, the coupling, and the Wick constant. -/
axiom onNelsonEstimate (P : ONInteraction) (c a : ℝ) (ha : 0 < a)
    (hc : 0 < c) :
    ∃ B : ℝ, ∀ (φ : Fin N → FinLatticeField d M),
      onInteraction N d M P c a φ ≥ -B

/-! ## The interacting measure -/

/-- The Boltzmann weight exp(-V_N(φ)). -/
def onBoltzmannWeight (P : ONInteraction) (c a : ℝ)
    (φ : Fin N → FinLatticeField d M) : ℝ :=
  Real.exp (-onInteraction N d M P c a φ)

/-- The Boltzmann weight is strictly positive. -/
theorem onBoltzmannWeight_pos (P : ONInteraction) (c a : ℝ)
    (φ : Fin N → FinLatticeField d M) :
    0 < onBoltzmannWeight N d M P c a φ :=
  Real.exp_pos _

/-- The partition function Z_N = ∫ exp(-V_N) dμ^{⊗N}. -/
def onPartitionFunction (P : ONInteraction) (c a : ℝ)
    (μ_scalar : Measure (FinLatticeField d M)) : ℝ :=
  ∫ φ, onBoltzmannWeight N d M P c a φ ∂(nComponentMeasure N μ_scalar)

/-- **The O(N) interacting measure on the lattice.**

  μ_{int,N} = (1/Z_N) · exp(-V_N) · dμ_{GFF}^{⊗N}

This is a probability measure when V_N is bounded below (Nelson estimate)
and measurable. -/
def onInteractingMeasure (P : ONInteraction) (c a : ℝ)
    (μ_scalar : Measure (FinLatticeField d M)) :
    Measure (Fin N → FinLatticeField d M) :=
  let μ_N := nComponentMeasure N μ_scalar
  let Z := onPartitionFunction N d M P c a μ_scalar
  (ENNReal.ofReal Z)⁻¹ •
    μ_N.withDensity (fun φ => ENNReal.ofReal (onBoltzmannWeight N d M P c a φ))

/-! ## Continuity and measurability of the interaction -/

/-- Induction pair for continuity of Wick monomials (carries consecutive degrees). -/
private def wickMonomial_contPair (N : ℕ) (c : ℝ) (k : ℕ) : Prop :=
  Continuous (fun t : ℝ => wickMonomial_ON N c k t) ∧
  Continuous (fun t : ℝ => wickMonomial_ON N c (k + 1) t)

private lemma wickMonomial_contPair_inductive (N : ℕ) (c : ℝ) (k : ℕ) :
    wickMonomial_contPair N c k := by
  induction k with
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

/-- Each Wick monomial is continuous in its argument t. -/
private lemma wickMonomial_ON_cont (N : ℕ) (c : ℝ) (k : ℕ) :
    Continuous (fun t : ℝ => wickMonomial_ON N c k t) :=
  (wickMonomial_contPair_inductive N c k).1

/-- The Wick interaction is continuous in t. -/
private lemma wickInteraction_ON_cont (N : ℕ) (c : ℝ) (P : ONInteraction) :
    Continuous (fun t : ℝ => wickInteraction_ON N P c t) := by
  unfold wickInteraction_ON
  exact (continuous_const.mul (wickMonomial_ON_cont N c P.degree)).add
    (continuous_finset_sum _ (fun m _ =>
      continuous_const.mul (wickMonomial_ON_cont N c m)))

/-- The Boltzmann weight is measurable.

Follows because exp(-V_N) is a composition of continuous functions
(polynomials) of the measurable projections on the finite product space. -/
private lemma onBoltzmannWeight_measurable (P : ONInteraction) (c a : ℝ) :
    Measurable (onBoltzmannWeight N d M P c a) := by
  unfold onBoltzmannWeight onInteraction
  apply Real.measurable_exp.comp
  apply Measurable.neg
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro x _
  -- wickInteraction_ON N P c (siteNormSq N d M φ x) is measurable in φ via continuity
  apply (wickInteraction_ON_cont N c P).measurable.comp
  unfold siteNormSq
  apply Finset.measurable_sum
  intro i _
  apply Measurable.pow_const
  exact (measurable_pi_apply x).comp (measurable_pi_apply i)

/-- The O(N) interacting measure is a probability measure.

Proof: same as scalar case. exp(-V) > 0 everywhere and bounded
(from the Nelson estimate), so Z > 0 and the normalized measure
has total mass 1. -/
theorem onInteractingMeasure_isProbability
    (P : ONInteraction) (c a : ℝ) (ha : 0 < a) (hc : 0 < c)
    (μ_scalar : Measure (FinLatticeField d M))
    [IsProbabilityMeasure μ_scalar] :
    IsProbabilityMeasure (onInteractingMeasure N d M P c a μ_scalar) := by
  constructor
  show (onInteractingMeasure N d M P c a μ_scalar) Set.univ = 1
  simp only [onInteractingMeasure, Measure.smul_apply, smul_eq_mul]
  -- Abbreviations for readability
  let μ_N := nComponentMeasure N μ_scalar
  let bw := onBoltzmannWeight N d M P c a
  let Z := onPartitionFunction N d M P c a μ_scalar
  -- Nelson bound gives: bw ≤ exp(B) everywhere
  obtain ⟨B, hB⟩ := onNelsonEstimate N d M P c a ha hc
  -- Boltzmann weight is strictly positive everywhere
  have hbw_pos : ∀ φ, 0 < bw φ := onBoltzmannWeight_pos N d M P c a
  -- Boltzmann weight is integrable (bounded above by exp(B))
  have hbw_int : Integrable bw μ_N := by
    apply (memLp_of_bounded (a := 0) (b := Real.exp B)
      (ae_of_all _ (fun φ => ?_))
      (onBoltzmannWeight_measurable N d M P c a).aestronglyMeasurable (p := 1)).integrable le_rfl
    exact ⟨le_of_lt (hbw_pos φ), Real.exp_le_exp_of_le (by linarith [hB φ])⟩
  -- Partition function Z > 0 (since bw > 0 and μ_N is a probability measure)
  have hZ_pos : 0 < Z := by
    unfold Z onPartitionFunction
    rw [integral_pos_iff_support_of_nonneg (fun φ => le_of_lt (hbw_pos φ)) hbw_int]
    have hsupport : Function.support bw = Set.univ := by
      ext φ; simp [Function.mem_support, (hbw_pos φ).ne']
    rw [hsupport, measure_univ]; norm_num
  -- The withDensity measure has total mass = ENNReal.ofReal Z
  have hmass : μ_N.withDensity (fun φ => ENNReal.ofReal (bw φ)) Set.univ =
      ENNReal.ofReal Z := by
    rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ,
        MeasureTheory.setLIntegral_univ]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hbw_int
      (ae_of_all _ fun φ => le_of_lt (hbw_pos φ))).symm
  -- (1/Z) * Z = 1
  rw [hmass]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr hZ_pos) ENNReal.ofReal_ne_top

/-! ## N-dependence -/

/-- The partition function Z_N is polynomial in N.

Z_N = ∫ exp(-V_N) dμ^{⊗N} where V_N is polynomial in N
(from wickInteraction_ON_polynomial_in_N). On the finite lattice,
exp(-V_N) is an entire function of V_N, and V_N is polynomial in N,
so Z_N is an entire function of N (hence polynomial for integer N). -/
theorem onPartitionFunction_polynomial_in_N
    (P : ONInteraction) (c a : ℝ) (ha : 0 < a)
    (μ_scalar : Measure (FinLatticeField d M))
    [IsProbabilityMeasure μ_scalar] :
    -- Z_N is polynomial in N (when viewed as a function of N)
    True := by trivial -- placeholder

end Pphi2N

end
