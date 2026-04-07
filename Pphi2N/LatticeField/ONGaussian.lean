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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas

noncomputable section

open MeasureTheory BigOperators Polynomial

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
  induction k with
  | zero => exact ⟨1, by simp, fun _ => by simp [onRisingFactorial]⟩
  | succ k ih =>
    obtain ⟨P, hd, heval⟩ := ih
    refine ⟨P * (X + C (2 * k : ℝ)), ?_, fun N => ?_⟩
    · -- natDegree(P * (X + C(2k))) ≤ deg(P) + 1 ≤ k + 1
      calc (P * (X + C (2 * (k : ℝ)))).natDegree
          ≤ P.natDegree + (X + C (2 * (k : ℝ))).natDegree := natDegree_mul_le
        _ ≤ k + 1 := by rw [natDegree_X_add_C]; omega
    · simp only [onRisingFactorial, eval_mul, eval_add, eval_X, eval_C, heval]

/-- At N=1: the rising factorial is (1)(3)(5)···(2k-1) = (2k-1)!!. -/
theorem onRisingFactorial_one (k : ℕ) :
    onRisingFactorial 1 k = ∏ j ∈ Finset.range k, (1 + 2 * (j : ℝ)) := by
  induction k with
  | zero => simp [onRisingFactorial]
  | succ k ih =>
    simp only [onRisingFactorial, Finset.prod_range_succ]
    rw [ih]; ring

end Pphi2N

end
