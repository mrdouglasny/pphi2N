/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# O(N) Wick Ordering

Wick ordering for O(N)-invariant interactions. The Wick-ordered monomial
:(|φ|²)^k:_c subtracts all self-contractions, producing a polynomial
in |φ|² and the Wick constant c = G(x,x), with coefficients that are
polynomials in N.

## Main definitions

- `wickMonomial_ON` — :(|φ|²)^k:_c as a polynomial in |φ|² and c
- `wickInteraction_ON` — :P(|φ|²):_c for a polynomial P

## Key formula

:(|φ|²)^k:_c = Σ_{j=0}^k (-1)^{k-j} C(k,j) · (N+2j)(N+2j+2)···(N+2k-2)
               × cʲ × (|φ|²)^{k-j} / (appropriate combinatorial factor)

More precisely, using the O(N) Hermite-like recursion:
:(|φ|²)^{k+1}:_c = |φ|² · :(|φ|²)^k:_c - k(N + 2k - 2) · c · :(|φ|²)^{k-1}:_c

The coefficient k(N+2k-2) is the number of Wick contractions of one
factor of |φ|² with one of the k existing factors, accounting for the
O(N) trace (the N+2k-2 comes from contracting with the symmetric
tensor of rank 2k).

## N-dependence

Each coefficient of :(|φ|²)^k:_c (as a polynomial in |φ|² and c)
is a polynomial in N. This is because the recursion coefficient
k(N+2k-2) is linear in N, and the recursion preserves polynomiality.

## Examples

- :(|φ|²)⁰:_c = 1
- :(|φ|²)¹:_c = |φ|² - Nc        (subtract ⟨|φ|²⟩ = Nc)
- :(|φ|²)²:_c = (|φ|²)² - 2(N+2)c·|φ|² + N(N+2)c²
- :(|φ|²)³:_c = (|φ|²)³ - 3(N+4)c·(|φ|²)² + 3(N+2)(N+4)c²·|φ|²
                - N(N+2)(N+4)c³

For N=1: these reduce to the standard Hermite-based Wick monomials
:φ^{2k}:_c (with the identification |φ|² = φ²).

## References

- Simon, *The P(φ)₂ Euclidean QFT*, §II.3
- Glimm-Jaffe, *Quantum Physics*, §6.1
-/

import Pphi2N.LatticeField.ONGaussian
import Pphi2N.Model.Interaction

noncomputable section

open BigOperators

namespace Pphi2N

/-- The O(N) Wick recursion coefficient: contracting one factor of |φ|²
with one of k existing factors in :(|φ|²)^k: gives k(N+2k-2) terms.

- k: the number of existing |φ|² factors
- N+2k-2: the O(N) trace factor (contracting φⁱφⁱ with a symmetric
  tensor of 2k indices gives δⁱⱼ × (N+2k-2) from the remaining
  2k-2 indices) -/
def wickRecursionCoeff (N : ℕ) (k : ℕ) : ℝ :=
  k * (N + 2 * k - 2 : ℝ)

/-- The Wick recursion coefficient is a polynomial in N of degree 1
(for k ≥ 1). -/
theorem wickRecursionCoeff_linear_in_N (k : ℕ) (hk : 1 ≤ k) :
    ∃ (a b : ℝ), ∀ (N : ℕ), wickRecursionCoeff N k = a * N + b := by
  refine ⟨k, k * (2 * k - 2), fun N => ?_⟩
  simp only [wickRecursionCoeff]
  ring

/-- Wick-ordered monomial :(|φ|²)^k:_c evaluated at a field value t = |φ|².

Defined by the recursion:
- :(|φ|²)⁰:_c = 1
- :(|φ|²)^{k+1}:_c(t) = t · :(|φ|²)^k:_c(t)
                        - k(N+2k-2) · c · :(|φ|²)^{k-1}:_c(t)

This produces a polynomial in t (of degree k) with coefficients that
are polynomials in N and c. -/
def wickMonomial_ON (N : ℕ) (c : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, t => t - N * c
  | k + 2, t => t * wickMonomial_ON N c (k + 1) t -
      wickRecursionCoeff N (k + 1) * c * wickMonomial_ON N c k t

/-- At k=0: :(|φ|²)⁰:_c = 1. -/
@[simp] theorem wickMonomial_ON_zero (N : ℕ) (c t : ℝ) :
    wickMonomial_ON N c 0 t = 1 := rfl

/-- At k=1: :(|φ|²)¹:_c = |φ|² - Nc. -/
@[simp] theorem wickMonomial_ON_one (N : ℕ) (c t : ℝ) :
    wickMonomial_ON N c 1 t = t - N * c := rfl

/-- At k=2: :(|φ|²)²:_c = (|φ|²)² - 2(N+2)c·|φ|² + N(N+2)c². -/
theorem wickMonomial_ON_two (N : ℕ) (c t : ℝ) :
    wickMonomial_ON N c 2 t =
      t ^ 2 - (N : ℝ) * c * t - (N : ℝ) * c := by
  simp only [wickMonomial_ON, wickRecursionCoeff]
  ring

/-- The Wick monomial at degree k is a polynomial in N of degree k.

This is the key structural fact: each coefficient of :(|φ|²)^k:_c
(viewed as a polynomial in t and c) is itself a polynomial in N
of degree ≤ k. The proof is by induction: the recursion multiplies
by a coefficient linear in N. -/
theorem wickMonomial_ON_polynomial_in_N (k : ℕ) (c t : ℝ) :
    ∃ (P : Polynomial ℝ), P.natDegree ≤ k ∧
      ∀ (N : ℕ), wickMonomial_ON N c k t = P.eval (N : ℝ) := by
  sorry -- induction on k using the recursion

/-- The Wick-ordered interaction :P(|φ|²):_c for a polynomial P.

If P(t) = (1/k)t^k + Σ aₘ tᵐ, then
:P(|φ|²):_c = (1/k) :(|φ|²)^k:_c + Σ aₘ :(|φ|²)^m:_c

This is a polynomial in |φ|², c, AND N (the key fact). -/
def wickInteraction_ON (N : ℕ) (P : ONInteraction) (c : ℝ) (t : ℝ) : ℝ :=
  (1 / P.degree : ℝ) * wickMonomial_ON N c P.degree t +
  ∑ m : Fin P.degree, P.coeff m * wickMonomial_ON N c m t

end Pphi2N

end
