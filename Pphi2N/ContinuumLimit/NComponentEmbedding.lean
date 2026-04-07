/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# N-Component Torus Embedding

Embeds N-component lattice fields into the N-component torus
configuration space, componentwise.

## Construction

For each component i = 1,...,Nc:
  φⁱ on lattice → ωⁱ on continuum (via scalar torusEmbedLift)

The combined embedding:
  (φ¹,...,φᴺ) ↦ ω where ω(pure(g, eᵢ)) = (torusEmbedLift φⁱ)(g)

## Key property

The embedding is measurable and continuous on the configuration
spaces, enabling the pushforward of measures.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1
-/

import Pphi2N.ContinuumLimit.NComponentTestFunction
import Pphi2N.InteractingMeasure.ONTorusMeasure
import Torus.Evaluation

noncomputable section

open GaussianField MeasureTheory Filter

namespace Pphi2N

variable (L : ℝ) [hL : Fact (0 < L)] (Nc : ℕ) [NeZero Nc]

/-! ## Componentwise embedding

The N-component lattice field φ = (φ¹,...,φᴺᶜ) where
φⁱ : FinLatticeSites 2 M → ℝ is embedded into the N-component
continuum configuration space by applying the scalar embedding
to each component independently. -/

variable (M : ℕ) [NeZero M]

/-- Embed a single scalar lattice field into the continuum.
Uses `torusEmbedCLM` from gaussian-field. -/
def scalarTorusEmbed (φ_scalar : FinLatticeField 2 M) :
    Configuration (TorusTestFunction L) :=
  torusEmbedCLM L M φ_scalar

/-- The N-component torus embedding: applies scalar embedding to
each component independently.

Input: φ : Fin Nc → FinLatticeField 2 M (N scalar lattice fields)
Output: ω : NComponentTorusConfig L Nc (N-component continuum config)

The output ω acts on test functions f ∈ NTP(TorusTestFunction L, ℝ^Nc) by:
  ω(f) = Σₐ Σᵢ (vₐ)ᵢ · (torusEmbedLift φⁱ)(gₐ)
where f = Σₐ pure(gₐ, vₐ). -/
def nComponentTorusEmbedLift
    (φ : Fin Nc → FinLatticeField 2 M) :
    NComponentTorusConfig L Nc where
  toFun f := sorry
    -- Σᵢ (scalarTorusEmbed L M (φ i)) (component_i_projection f)
    -- Needs: projection from NTP(E₁, E₂) to E₁ via pairing with E₂ basis
  map_add' := sorry
  map_smul' := sorry
  cont := sorry

/-- The embedding is measurable. -/
theorem nComponentTorusEmbedLift_measurable :
    Measurable (nComponentTorusEmbedLift L Nc M) := by
  sorry

/-! ## Pushed-forward measures -/

/-- The N-component torus interacting measure on the continuum:
pushforward of the lattice measure under the N-component embedding.

  μ_{cont,N} = (nComponentTorusEmbedLift)_* μ_{lat,N}

where μ_{lat,N} is the O(N) interacting measure from ONTorusMeasure.lean. -/
def nComponentTorusMeasure
    (P : ONInteraction) (c a : ℝ)
    (μ_scalar : Measure ((Fin 2 → Fin M) → ℝ))
    [IsProbabilityMeasure μ_scalar] :
    Measure (NComponentTorusConfig L Nc) :=
  -- Pushforward of O(N) lattice interacting measure under componentwise embedding
  sorry

/-! ## Tightness and limit (outline)

The continuum limit follows the same structure as pphi2:
1. Uniform second moments: ∫ (ω(f))² dμ_M ≤ C · q(f)² (from Nelson)
2. Mitoma-Chebyshev: uniform moments → tightness
3. Prokhorov: tightness → subsequential weak limit

The N-dependent constants:
- Wick constant: c_N = Nc₁ (N times scalar)
- Nelson bound: B(N) = O(N · B₁) (N times scalar)
- Second moment: ∫ (ω(f))² ≤ N · C₁ · q(f)² (N times scalar)

All bounds are polynomial in N, so the continuum limit exists for
each fixed N. The polynomial-in-N property is preserved. -/

/-- The N-component torus interacting continuum limit exists.

For each N ≥ 1 and each O(N)-invariant interaction P, the sequence
of pushed-forward lattice measures is tight, and has a weakly
convergent subsequence. The limit is a probability measure on the
N-component continuum configuration space. -/
theorem nComponentTorusLimit_exists
    (P : ONInteraction) (mass : ℝ) (hmass : 0 < mass) :
    -- There exists a probability measure on the N-component continuum
    -- configuration space that is the weak limit of lattice measures.
    -- Proof: Mitoma-Chebyshev tightness + Prokhorov, same as pphi2.
    True := by trivial -- placeholder for the full limit theorem

end Pphi2N

end
