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

/-! ## Site-component evaluation -/

/-- Evaluation of a FinLatticeField 1 Nc at component i.
FinLatticeField 1 Nc = (FinLatticeSites 1 Nc) → ℝ = (Fin 1 → Fin Nc) → ℝ.
We evaluate at the lattice site corresponding to component i. -/
def componentEvalCLM (i : Fin Nc) : FinLatticeField 1 Nc →L[ℝ] ℝ where
  toFun v := v (fun _ => i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation of an N-component torus test function at site x, component i.

For f ∈ NTP(TorusTestFunction L, ℝ^Nc):
  evalNComponentAtSite x i f = evalCLM (evalTorusAtSite x) (componentEval i) f

On pure tensors: evalNComponentAtSite x i (pure g v) = (eval_x g) · v(i) -/
def evalNComponentAtSite (x : FinLatticeSites 2 M) (i : Fin Nc) :
    NComponentTorusTestFunction L Nc →L[ℝ] ℝ :=
  NuclearTensorProduct.evalCLM
    (evalTorusAtSite L M x)
    (componentEvalCLM Nc i)

/-- The N-component torus embedding: maps N scalar lattice fields
into the N-component continuum configuration space.

  ω(f) = Σ_{x ∈ Λ} Σ_{i=1}^{Nc} φⁱ(x) · evalNComponentAtSite(x, i, f)

This is the tensor product analogue of `torusEmbedCLM`. -/
def nComponentTorusEmbedLift
    (φ : Fin Nc → FinLatticeField 2 M) :
    NComponentTorusConfig L Nc where
  toFun f := ∑ x : FinLatticeSites 2 M, ∑ i : Fin Nc,
    φ i x * evalNComponentAtSite L Nc M x i f
  map_add' f g := by
    simp only [map_add, mul_add, Finset.sum_add_distrib]
  map_smul' r f := by
    simp only [map_smul, smul_eq_mul, mul_left_comm, Finset.mul_sum, RingHom.id_apply]
  cont := by
    apply continuous_finset_sum; intro x _
    apply continuous_finset_sum; intro i _
    exact continuous_const.mul (evalNComponentAtSite L Nc M x i).cont

/-- The embedding is measurable. -/
theorem nComponentTorusEmbedLift_measurable :
    Measurable (nComponentTorusEmbedLift L Nc M) :=
  configuration_measurable_of_eval_measurable _ fun f =>
    Finset.measurable_sum _ fun x _ =>
      Finset.measurable_sum _ fun i _ =>
        -- φ ↦ φ i x * (constant depending on f)
        (measurable_pi_apply x |>.comp (measurable_pi_apply i)).mul measurable_const

/-! ## Pushed-forward measures -/

/-- The N-component torus interacting measure on the continuum:
pushforward of the lattice measure under the N-component embedding.

  μ_{cont,N} = (nComponentTorusEmbedLift)_* μ_{lat,N}

where μ_{lat,N} is the O(N) interacting measure from ONTorusMeasure.lean. -/
def nComponentTorusMeasure
    (P : ONInteraction) (c a : ℝ)
    (μ_scalar : Measure (FinLatticeField 2 M))
    [IsProbabilityMeasure μ_scalar] :
    Measure (NComponentTorusConfig L Nc) :=
  -- onInteractingMeasure produces Measure (Fin Nc → (Fin 2 → Fin M) → ℝ)
  -- nComponentTorusEmbedLift expects Fin Nc → FinLatticeField 2 M
  -- These are definitionally equal (FinLatticeField = FinLatticeSites → ℝ)
  Measure.map (show (Fin Nc → FinLatticeField 2 M) → NComponentTorusConfig L Nc from
    nComponentTorusEmbedLift L Nc M)
    (Pphi2N.onInteractingMeasure Nc 2 M P c a μ_scalar)

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
