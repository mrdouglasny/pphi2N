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

open GaussianField MeasureTheory BigOperators

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

/-- The O(N) interacting measure is a probability measure.

Proof: same as scalar case. exp(-V) > 0 everywhere and bounded
(from the Nelson estimate), so Z > 0 and the normalized measure
has total mass 1. -/
theorem onInteractingMeasure_isProbability
    (P : ONInteraction) (c a : ℝ) (ha : 0 < a) (hc : 0 < c)
    (μ_scalar : Measure (FinLatticeField d M))
    [IsProbabilityMeasure μ_scalar] :
    IsProbabilityMeasure (onInteractingMeasure N d M P c a μ_scalar) := by
  sorry -- from onNelsonEstimate + Z > 0 + normalization

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
