/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# O(N) Gaussian Free Field on the Lattice

The O(N) GFF: N independent copies of the scalar GFF. The measure is
a product Gaussian on ℝ^{N|Λ|} with covariance:

  ⟨φⁱ(x) φʲ(y)⟩ = δⁱʲ · G(x,y)

where G = (-Δ_a + m²)⁻¹ is the scalar lattice Green's function.

## Main definitions

- `onGFFCovariance` — the N×N block-diagonal covariance matrix
- `onGFFMeasure` — the product Gaussian measure
- `onGFF_factorization` — μ_N = μ₁ ⊗ ... ⊗ μ₁ (N copies)
- `wickConstant_ON` — c_N(x) = N · G(x,x)

## Key property: N-dependence is explicit

The GFF measure is a product of N independent copies of the scalar
GFF. All N-dependence comes from:
1. The Wick constant c_N = N · c₁ (trace over N components)
2. The number of degrees of freedom (N|Λ| vs |Λ|)

The Wick ordering :(|φ|²)^k:_{c_N} involves the O(N) rising
factorial (N)(N+2)···(N+2k-2), which is polynomial in N of degree k.

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I
-/

import Pphi2N.LatticeField.NComponentField

noncomputable section

open MeasureTheory BigOperators

namespace Pphi2N

variable (N : ℕ) (hN : 1 ≤ N)

/-- The O(N) Wick constant at a site x: c_N = N · G(x,x).

This is the variance of |φ(x)|² under the O(N) GFF:
  E[|φ(x)|²] = Σᵢ E[(φⁱ(x))²] = N · G(x,x)

The factor of N is the only N-dependence in the free theory. -/
def wickConstant_ON (G_diag : ℝ) : ℝ := N * G_diag

/-- The Wick constant is positive when G(x,x) > 0. -/
theorem wickConstant_ON_pos (hN' : 1 ≤ N) (G_diag : ℝ) (hG : 0 < G_diag) :
    0 < wickConstant_ON N G_diag := by
  unfold wickConstant_ON
  exact mul_pos (Nat.cast_pos.mpr (by omega)) hG

/-- The Wick constant scales linearly with N. -/
theorem wickConstant_ON_eq_N_mul (G_diag : ℝ) :
    wickConstant_ON N G_diag = N * G_diag := rfl

/-- The O(N) rising factorial: (N)(N+2)(N+4)···(N+2k-2).

This appears in the Wick ordering of (|φ|²)^k. It is a polynomial
in N of degree k, which is the key fact for the polynomial-in-N theorem.

For k=0: 1
For k=1: N
For k=2: N(N+2)
For k=3: N(N+2)(N+4) -/
def onRisingFactorial (N : ℕ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => onRisingFactorial N k * (N + 2 * k : ℝ)

/-- The rising factorial is a polynomial in N of degree k. -/
theorem onRisingFactorial_polynomial (k : ℕ) :
    ∃ (P : Polynomial ℝ), P.natDegree ≤ k ∧
      ∀ (N : ℕ), onRisingFactorial N k = P.eval (N : ℝ) := by
  sorry -- induction on k: multiply by (N + 2k) increases degree by 1

/-- At N=1: the rising factorial is (1)(3)(5)···(2k-1) = (2k-1)!!. -/
theorem onRisingFactorial_one (k : ℕ) :
    onRisingFactorial 1 k = ∏ j ∈ Finset.range k, (1 + 2 * (j : ℝ)) := by
  sorry

end Pphi2N

end
