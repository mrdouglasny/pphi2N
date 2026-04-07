/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# N-Component Lattice Fields

Lattice fields with N real components at each site. The field
configuration is φ : Λ → ℝ^N where Λ is a finite lattice.

## Main definitions

- `NComponentField` — type alias for N-component lattice fields
- `fieldNormSq` — |φ(x)|² = Σᵢ (φⁱ(x))²
- `totalFieldNormSq` — Σ_x |φ(x)|² (total squared norm)
- `singleComponent` — extract the i-th component as a scalar field

## O(N) action

O(N) acts on N-component fields by rotating the internal index:
(g · φ)(x) = g (φ(x)) for g ∈ O(N), x ∈ Λ.

The squared norm |φ(x)|² is O(N)-invariant:
|g · φ(x)|² = |φ(x)|² for all g ∈ O(N).

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.MeasureSpace

noncomputable section

open BigOperators Finset

namespace Pphi2N

variable (N : ℕ) (Λ : Type*) [Fintype Λ]

/-- An N-component lattice field: at each site x ∈ Λ, the field has
N real components φ¹(x), ..., φᴺ(x).

Equivalently: a function Λ → (Fin N → ℝ), or (Fin N × Λ → ℝ). -/
abbrev NComponentField := Λ → (Fin N → ℝ)

/-- The squared norm of the field at a single site:
|φ(x)|² = Σᵢ (φⁱ(x))². -/
def fieldNormSq (φ : NComponentField N Λ) (x : Λ) : ℝ :=
  ∑ i : Fin N, (φ x i) ^ 2

/-- |φ(x)|² ≥ 0. -/
theorem fieldNormSq_nonneg (φ : NComponentField N Λ) (x : Λ) :
    0 ≤ fieldNormSq N Λ φ x :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The total squared norm: Σ_x |φ(x)|² (lattice integral of |φ|²). -/
def totalFieldNormSq (φ : NComponentField N Λ) : ℝ :=
  ∑ x : Λ, fieldNormSq N Λ φ x

/-- Extract the i-th component as a scalar field φⁱ : Λ → ℝ. -/
def singleComponent (φ : NComponentField N Λ) (i : Fin N) : Λ → ℝ :=
  fun x => φ x i

/-- The squared norm equals the sum of squared components:
|φ(x)|² = Σᵢ (φⁱ(x))². -/
theorem fieldNormSq_eq_sum_sq (φ : NComponentField N Λ) (x : Λ) :
    fieldNormSq N Λ φ x = ∑ i : Fin N, (singleComponent N Λ φ i x) ^ 2 := by
  rfl

end Pphi2N

end
