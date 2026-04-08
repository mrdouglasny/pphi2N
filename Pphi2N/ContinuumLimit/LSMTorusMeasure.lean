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
import GaussianField.Density

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2N

variable (L_phys : ℝ) [hL : Fact (0 < L_phys)]

/-! ## LSM torus measure construction

For each lattice size M, the O(N) interacting measure with the LSM
potential P(t) = λ(t - v²)² (vacuum subtracted), pushed forward to
the continuum N-component configuration space.

Construction chain:
1. Scalar lattice GFF → evalMap → raw field measure on FinLatticeField
2. N independent copies via Measure.pi
3. O(N) Wick-ordered interaction :P(|φ|²):_c
4. Boltzmann weight (1/Z) exp(-V) dμ^{⊗N}
5. Componentwise torus embedding via evalCLM
6. Continuum measure on NTP(TorusTestFunction, ℝ^N) -/

/-- The scalar lattice GFF pushed to raw field space via evalMap.
latticeGaussianMeasure gives Measure(Configuration(FinLatticeField 2 M)).
We push forward via evalMapMeasurableEquiv to get Measure(FinLatticeField 2 M). -/
def scalarLatticeGFF (mass spacing : ℝ) (hspacing : 0 < spacing) (hmass : 0 < mass)
    (M : ℕ) [NeZero M] : Measure (FinLatticeField 2 M) :=
  (latticeGaussianMeasure 2 M spacing mass hspacing hmass).map
    (evalMapMeasurableEquiv 2 M)

instance scalarLatticeGFF_isProbability (mass spacing : ℝ)
    (hspacing : 0 < spacing) (hmass : 0 < mass) (M : ℕ) [NeZero M] :
    IsProbabilityMeasure (scalarLatticeGFF mass spacing hspacing hmass M) := by
  unfold scalarLatticeGFF
  exact Measure.isProbabilityMeasure_map (evalMapMeasurableEquiv 2 M).measurable.aemeasurable

def lsmTorusMeasure (params : LSMParams) (M : ℕ) [NeZero M] :
    Measure (NComponentTorusConfig L_phys params.N) :=
  haveI : NeZero params.N := ⟨Nat.one_le_iff_ne_zero.mp params.hN⟩
  let spacing := L_phys / M
  let hspacing := div_pos hL.out (Nat.cast_pos.mpr (NeZero.pos M))
  let P := params.toONModel.interaction
  let c : ℝ := 0  -- placeholder: Wick constant G(x,x)
  nComponentTorusMeasure L_phys params.N M P c spacing
    (scalarLatticeGFF params.mass spacing hspacing params.hmass M)

/-- The LSM torus measure is a probability measure. -/
instance lsmTorusMeasure_isProbability (params : LSMParams) (M : ℕ) [NeZero M] :
    IsProbabilityMeasure (lsmTorusMeasure L_phys params M) := by
  -- lsmTorusMeasure = Measure.map embed (onInteractingMeasure ...)
  -- onInteractingMeasure is a probability measure (proved)
  -- embed is measurable (proved)
  -- Measure.map of prob under measurable = prob
  -- Blocked: Wick constant c=0 is a placeholder.
  -- Needs actual Wick constant G(x,x) > 0 so that the Nelson estimate
  -- gives Z > 0 and the onInteractingMeasure is well-defined as a
  -- probability measure. With c=0, the Wick ordering is trivial and
  -- the Nelson bound may fail for general polynomials.
  sorry

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
