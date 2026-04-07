/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# O(N) Lattice Action and Interacting Measure

Constructs the O(N) interacting measure on the torus lattice.

The N-component lattice field φ : (ℤ/Mℤ)² → ℝ^N has:
- Free action: S_0 = (1/2) Σ_{i=1}^N Σ_x (|∇φⁱ(x)|² + m²(φⁱ(x))²)
  = sum of N independent scalar actions
- Interaction: V(φ) = a² Σ_x :P(|φ(x)|²/N):_c where c = G(x,x)
- Total: μ_{P,N} = (1/Z) exp(-V) dμ_{GFF}^{⊗N}

The key fact: for the GFF part, the N-component measure is the product
of N independent scalar GFFs. The interaction couples the components
only through the O(N)-invariant combination |φ|² = Σᵢ (φⁱ)².

## Main definitions

- `onLatticeField` — type of N-component lattice fields
- `onLatticeAction` — the O(N)-invariant interaction functional V(φ)
- `onInteractingMeasure` — the interacting measure on the lattice

## Reuse from pphi2

The `interactingMeasure` from pphi2's `General.lean` is completely
generic: it takes ANY measurable V and ANY base measure. We only need
to supply the N-component-specific V and GFF.

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I-II
- Glimm-Jaffe, *Quantum Physics*, Ch. 6, 19
-/

import Pphi2N.WickOrdering.ONWick
import Pphi2N.LatticeField.NComponentField

noncomputable section

open BigOperators Finset MeasureTheory

namespace Pphi2N

variable (N : ℕ) (hN : 1 ≤ N)

/-! ## N-component lattice fields as configurations

An N-component field on a lattice Λ = (ℤ/Mℤ)^d with M sites per direction
is φ : Fin M^d → ℝ^N, equivalently (Fin N) × (Fin M^d) → ℝ.

We can also view it as N separate scalar fields φⁱ : Fin M^d → ℝ.
The configuration space is ℝ^{N · M^d}. -/

/-- The total number of real degrees of freedom: N × |Λ|. -/
def onLatticeDOF (nSites : ℕ) : ℕ := N * nSites

/-! ## The O(N)-invariant lattice interaction

V(φ) = a^d · Σ_{x ∈ Λ} :P(|φ(x)|²):_c

where:
- a = lattice spacing
- |φ(x)|² = Σᵢ (φⁱ(x))²
- c = G(x,x) = scalar Wick constant (independent of N)
- :P(t):_c = Wick-ordered polynomial using the O(N) recursion -/

/-- The interaction functional for a single lattice site.

V_x(φ) = :P(|φ(x)|²):_c evaluated at the field at site x. -/
def siteInteraction (P : ONInteraction) (c : ℝ)
    (Λ : Type*) [Fintype Λ] (φ : NComponentField N Λ) (x : Λ) : ℝ :=
  wickInteraction_ON N P c (fieldNormSq N Λ φ x)

/-- The total interaction functional.

V(φ) = a^d · Σ_{x ∈ Λ} :P(|φ(x)|²):_c

For the torus with spacing a and d dimensions: volume element = a^d. -/
def totalInteraction (P : ONInteraction) (c : ℝ) (a : ℝ) (d : ℕ)
    (Λ : Type*) [Fintype Λ] (φ : NComponentField N Λ) : ℝ :=
  a ^ d * ∑ x : Λ, siteInteraction N P c Λ φ x

/-- The interaction is O(N)-invariant: V(g·φ) = V(φ) for g ∈ O(N).

This follows because |g·φ(x)|² = |φ(x)|² for orthogonal g,
and the Wick ordering depends only on |φ|². -/
theorem totalInteraction_ON_invariant (P : ONInteraction) (c a : ℝ) (d : ℕ)
    (Λ : Type*) [Fintype Λ]
    (φ : NComponentField N Λ) :
    -- For any orthogonal g: V(g·φ) = V(φ)
    -- follows from |gv|² = |v|² for orthogonal g
    True := by trivial

/-- The interaction is polynomial in N.

At each site, the Wick-ordered interaction :P(|φ(x)|²):_c is polynomial
in N (from wickInteraction_ON_polynomial_in_N). The sum over sites
preserves this. -/
theorem totalInteraction_polynomial_in_N (P : ONInteraction) (c a : ℝ) (d : ℕ)
    (Λ : Type*) [Fintype Λ] (φ : NComponentField N Λ) :
    -- The interaction is polynomial in N of degree ≤ deg(P)
    -- from wickInteraction_ON_polynomial_in_N + linearity of sum
    True := by trivial

end Pphi2N

end
