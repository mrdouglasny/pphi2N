/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# N-Component Torus Test Functions

The N-component torus test function space:

  NComponentTorusTestFunction L Nc = NTP(TorusTestFunction L, ℝ^Nc)

where NTP is the nuclear tensor product and ℝ^Nc = FinLatticeField 1 Nc
is the target space (Nc real components).

A test function f ∈ NTP(TorusTestFunction L, ℝ^Nc) acts on N-component
fields by:
  φ(f) = Σᵢ φⁱ(fⁱ)
where f = Σ pure(gₐ, eᵢ) and fⁱ is the i-th component.

## DyninMityaginSpace instance

The nuclear tensor product of two DM spaces is automatically DM
(from gaussian-field's NuclearTensorProduct.dyninMityaginSpace).
Since both TorusTestFunction L and FinLatticeField 1 Nc are DM,
the tensor product inherits the DM structure.

## References

- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4
-/

import Pphi2N.LatticeField.NComponentField
import GaussianField.Construction
import Nuclear.NuclearTensorProduct
import Torus.Restriction
import Lattice.FiniteField

noncomputable section

open GaussianField

namespace Pphi2N

variable (L : ℝ) [hL : Fact (0 < L)] (Nc : ℕ) [NeZero Nc]

/-- The N-component torus test function space.

NTP(TorusTestFunction L, ℝ^Nc) — a nuclear Fréchet space with
DyninMityaginSpace instance inherited from the tensor product.

An element f represents an N-component test function on the torus T²_L:
f = Σ pure(gₐ, vₐ) where gₐ ∈ TorusTestFunction L and vₐ ∈ ℝ^Nc.

The pairing with an N-component field φ = (φ¹,...,φᴺ) is:
  φ(f) = Σᵢ φⁱ(fⁱ) where fⁱ = Σₐ (vₐ)ᵢ · gₐ -/
abbrev NComponentTorusTestFunction :=
  NuclearTensorProduct (TorusTestFunction L) (FinLatticeField 1 Nc)

/-- The N-component test function space is a DyninMityaginSpace.
This is automatic from the NTP instance. -/
example : DyninMityaginSpace (NComponentTorusTestFunction L Nc) := inferInstance

/-- The N-component configuration space: continuous linear functionals
on the test function space. An N-component distribution on T²_L. -/
abbrev NComponentTorusConfig :=
  Configuration (NComponentTorusTestFunction L Nc)

/-- Embed a scalar torus test function in component i:
g ↦ pure(g, eᵢ) where eᵢ is the i-th standard basis vector.

This gives the i-th component test function:
  φ(componentEmbed i g) = φⁱ(g) -/
def componentEmbed (i : Fin Nc) (g : TorusTestFunction L) :
    NComponentTorusTestFunction L Nc :=
  NuclearTensorProduct.pure g (finLatticeBasisVec 1 Nc i)

end Pphi2N

end
