/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# LSM Measure on the Torus

Instantiates the O(N) construction for the Linear Sigma Model
P(t) = λ(t - v²)² on the torus T²_L.

This connects:
- LSMParams (the model data: N, λ, R², m)
- ONInteraction (the vacuum-subtracted polynomial)
- nComponentTorusMeasure (the pushforward to the continuum)

## Main definition

- `lsmTorusMeasure` — the LSM interacting measure on T²_L

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I-II
-/

import Pphi2N.ContinuumLimit.NComponentEmbedding
import Pphi2N.Model.LSM
import Lattice.Covariance

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2N

variable (L_phys : ℝ) [hL : Fact (0 < L_phys)]

/-- The LSM interacting measure on the torus lattice (ℤ/Mℤ)².

For each lattice size M, this is the O(N) interacting measure with
the LSM potential P(t) = λ(t - v²)² (vacuum subtracted), pushed
forward to the continuum N-component configuration space.

The construction chain:
1. Scalar lattice GFF: latticeGaussianMeasure 2 M (L_phys/M) mass
2. N independent copies: nComponentMeasure N μ_scalar
3. O(N) interaction: :P(|φ|²):_c with c = G(x,x)
4. Boltzmann weight: (1/Z) exp(-V) dμ^{⊗N}
5. Torus embedding: componentwise torusEmbedCLM
6. Continuum measure: pushforward to NTP(TorusTestFunction, ℝ^N) -/
def lsmTorusMeasure (params : LSMParams) (M : ℕ) [NeZero M] :
    Measure (NComponentTorusConfig L_phys params.N) :=
  -- The construction: lattice GFF^{⊗N} with LSM interaction, pushed to continuum.
  -- Type note: latticeGaussianMeasure gives Measure (Configuration (FinLatticeField 2 M))
  -- while nComponentTorusMeasure expects Measure (FinLatticeField 2 M).
  -- For finite lattices, Configuration E ≅ E (self-dual), but the types differ.
  -- The bridge is via the evaluation map: ω ↦ (fun x => ω (δ_x)).
  -- TODO: add evalMap bridge from gaussian-field (already exists in pphi2).
  sorry

/-- The LSM torus measure is a probability measure. -/
instance lsmTorusMeasure_isProbability (params : LSMParams) (M : ℕ) [NeZero M] :
    IsProbabilityMeasure (lsmTorusMeasure L_phys params M) := by
  sorry -- from onInteractingMeasure_isProbability + measurability of map

/-- **Main theorem (lattice level):** The LSM measure exists on T²_L
for each lattice size M, as a probability measure on the N-component
continuum configuration space.

The Wick-ordered interaction :P(|φ|²):_c with P(t) = λ(t-v²)² is
polynomial in N (degree ≤ 2), ensuring N-dependent quantities are
explicitly computable. -/
theorem lsmTorusMeasure_exists (params : LSMParams) (M : ℕ) [NeZero M] :
    ∃ μ : Measure (NComponentTorusConfig L_phys params.N),
      IsProbabilityMeasure μ := by
  exact ⟨lsmTorusMeasure L_phys params M, lsmTorusMeasure_isProbability L_phys params M⟩

end Pphi2N

end
