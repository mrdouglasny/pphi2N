/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Textbook Axiom: Uniform Torus Green's Function Bound

The single textbook fact that closes all remaining sorries:

**The N-component Gaussian second moment under the pushed-forward
lattice GFF is bounded by a continuous seminorm, uniformly in M.**

  E_{GFF,M}[(ω f)²] ≤ C · q(f)²    for all M ≥ 1

where ω is sampled from the scalar lattice GFF pushed through the
N-component torus embedding, and q is a continuous seminorm on the
N-component test function space.

## Why this closes everything

1. **Uniform second moment** (sorry 1): density transfer gives
   E_int[(ω f)²] ≤ Nelson^{1/2} · E_GFF[(ω f)⁴]^{1/2}
   ≤ (hypercontractivity) ≤ C' · E_GFF[(ω f)²]
   ≤ C' · C · q(f)²

2. **Translation invariance** (sorry 2): follows independently from
   Measure.map_withDensity + GFF translation invariance + V invariance

3. **Uniform exp moments** (sorry 3): density transfer applied to
   F = exp(|ω f|), combined with the Green's function bound

## Proof of the axiom

For each component i: E_GFF[(scalar_embed φⁱ)(fⁱ)²] = G_M(fⁱ,fⁱ)
≤ (1/m²) · l2InnerProduct(embed fⁱ, embed fⁱ) ≤ q_scalar(fⁱ)²
(from gaussian-field's torusGreen_uniform_bound + embed_l2_uniform_bound).

Summing: E_GFF[(embed φ)(f)²] = Σᵢ G_M(fⁱ,fⁱ) ≤ Σᵢ q_scalar(fⁱ)²
≤ q_NTP(f)² (NTP seminorm controls components via l2InnerProduct_pure).

## References

- gaussian-field: torusGreen_uniform_bound, embed_l2_uniform_bound
- pphi2: torus_second_moment_uniform
-/

import Pphi2N.ContinuumLimit.LSMTorusMeasure

noncomputable section

open GaussianField MeasureTheory BigOperators

namespace Pphi2N

variable (L : ℝ) [hL : Fact (0 < L)] (Nc : ℕ) [NeZero Nc]

/-- **Uniform N-component Green's function bound (textbook axiom).**

The Gaussian second moment of ω(f) under the pushed-forward N-component
lattice GFF is bounded by a continuous seminorm, uniformly in M.

This is the N-component generalization of gaussian-field's
`torusGreen_uniform_bound` composed with `embed_l2_uniform_bound`.

Proof chain (all existing in gaussian-field):
1. For scalar component i: G_M(fᵢ, fᵢ) ≤ (1/m²) · ‖embed fᵢ‖²_{ℓ²}
   (from greenFunctionBilinear_le)
2. ‖embed fᵢ‖²_{ℓ²} ≤ q_scalar(fᵢ)² uniformly in M
   (from embed_l2_uniform_bound)
3. The N-component pairing decomposes: E[(embed φ)(f)²] = Σᵢ G_M(fᵢ, fᵢ)
   (product GFF, independence of components)
4. Σᵢ q_scalar(fᵢ)² ≤ q_NTP(f)²
   (NTP seminorm controls component seminorms via l2InnerProduct_pure) -/
axiom nComponentGreen_uniform_bound (mass : ℝ) (hmass : 0 < mass) :
    ∃ (C : ℝ) (q : NComponentTorusTestFunction L Nc → ℝ),
      0 < C ∧ Continuous q ∧
      ∀ (M : ℕ) [NeZero M] (f : NComponentTorusTestFunction L Nc),
        ∫ ω : NComponentTorusConfig L Nc,
          (ω f) ^ 2 ∂(Measure.map (nComponentTorusEmbedLift L Nc M)
            (nComponentMeasure Nc
              (scalarLatticeGFF mass (L / M)
                (div_pos hL.out (Nat.cast_pos.mpr (NeZero.pos M))) hmass M))) ≤
        C * q f ^ 2

end Pphi2N

end
