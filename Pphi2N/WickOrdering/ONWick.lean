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

## Key recursion (Laguerre-type three-term)

:(|φ|²)^{k+1}:_c = (|φ|² - (N+4k)c) · :(|φ|²)^k:_c
                  - 2k(N+2k-2) · c² · :(|φ|²)^{k-1}:_c

This differs from the single-component Hermite recursion (:φ^{2k+2}: =
φ² · :φ^{2k}: - 2k·c · :φ^{2k-2}:) because the O(N) contractions
produce an N-dependent shift in the middle coefficient and an
N-dependent coefficient for the lower term.

## Examples

- :(|φ|²)⁰:_c = 1
- :(|φ|²)¹:_c = |φ|² - Nc
- :(|φ|²)²:_c = (|φ|²)² - 2(N+2)c·|φ|² + N(N+2)c²
- :(|φ|²)³:_c = (|φ|²)³ - 3(N+4)c·(|φ|²)² + 3(N+2)(N+4)c²·|φ|²
                - N(N+2)(N+4)c³

## N-dependence

Each coefficient of :(|φ|²)^k:_c (as a polynomial in |φ|² and c)
is a polynomial in N of degree ≤ k. This follows from the recursion:
the shift coefficient (N+4k) is linear in N, and the lower coefficient
2k(N+2k-2) is also linear in N, so inductively the degree in N
increases by at most 1 at each step.

The constant term is always the O(N) rising factorial:
:(0)^k:_c = (-1)^k · N(N+2)(N+4)···(N+2k-2) · c^k

## References

- Simon, *The P(φ)₂ Euclidean QFT*, §II.3
- Glimm-Jaffe, *Quantum Physics*, §6.1
-/

import Pphi2N.LatticeField.ONGaussian
import Pphi2N.Model.Interaction

noncomputable section

open BigOperators Polynomial

namespace Pphi2N

/-- The shift coefficient in the O(N) Wick recursion: β_k = N + 4k.

In the recursion T_{k+1} = (t - β_k·c) · T_k - γ_k · c² · T_{k-1},
the shift β_k accounts for the expected value E[|φ|² · :(|φ|²)^k:]
which involves the O(N) trace. -/
def wickShiftCoeff (N : ℕ) (k : ℕ) : ℝ :=
  (N : ℝ) + 4 * k

/-- The lower coefficient in the O(N) Wick recursion: γ_k = 2k(N + 2k - 2).

This counts the number of Wick contractions between the new |φ|²
factor and the k existing :(|φ|²)^k: factor, weighted by the O(N)
trace structure. -/
def wickLowerCoeff (N : ℕ) (k : ℕ) : ℝ :=
  2 * k * ((N : ℝ) + 2 * k - 2)

/-- Both recursion coefficients are polynomials in N of degree ≤ 1. -/
theorem wickShiftCoeff_linear (k : ℕ) :
    ∃ (a b : ℝ), ∀ (N : ℕ), wickShiftCoeff N k = a * N + b :=
  ⟨1, 4 * k, fun N => by simp [wickShiftCoeff]⟩

theorem wickLowerCoeff_linear (k : ℕ) :
    ∃ (a b : ℝ), ∀ (N : ℕ), wickLowerCoeff N k = a * N + b :=
  ⟨2 * k, 2 * k * (2 * k - 2), fun N => by simp [wickLowerCoeff]; ring⟩

/-- Wick-ordered monomial :(|φ|²)^k:_c evaluated at t = |φ|².

Defined by the Laguerre-type three-term recursion:
- T₀(t) = 1
- T₁(t) = t - Nc
- T_{k+2}(t) = (t - (N+4(k+1))c) · T_{k+1}(t) - 2(k+1)(N+2k) · c² · T_k(t) -/
def wickMonomial_ON (N : ℕ) (c : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, t => t - N * c
  | k + 2, t =>
      (t - wickShiftCoeff N (k + 1) * c) * wickMonomial_ON N c (k + 1) t -
      wickLowerCoeff N (k + 1) * c ^ 2 * wickMonomial_ON N c k t

/-- At k=0: :(|φ|²)⁰:_c = 1. -/
@[simp] theorem wickMonomial_ON_zero (N : ℕ) (c t : ℝ) :
    wickMonomial_ON N c 0 t = 1 := rfl

/-- At k=1: :(|φ|²)¹:_c = |φ|² - Nc. -/
@[simp] theorem wickMonomial_ON_one (N : ℕ) (c t : ℝ) :
    wickMonomial_ON N c 1 t = t - N * c := rfl

/-- At k=2: :(|φ|²)²:_c = (|φ|²)² - 2(N+2)c·|φ|² + N(N+2)c². -/
theorem wickMonomial_ON_two (N : ℕ) (c t : ℝ) :
    wickMonomial_ON N c 2 t =
      t ^ 2 - 2 * ((N : ℝ) + 2) * c * t + (N : ℝ) * ((N : ℝ) + 2) * c ^ 2 := by
  simp only [wickMonomial_ON, wickShiftCoeff, wickLowerCoeff]
  ring

/-! ## Helper lemmas for natDegree bounds -/

/-- A polynomial C(a) - C(b)*X has natDegree ≤ 1. -/
private lemma natDegree_C_sub_C_mul_X_le (a b : ℝ) :
    (Polynomial.C a - Polynomial.C b * Polynomial.X).natDegree ≤ 1 := by
  apply le_trans (natDegree_sub_le _ _)
  exact Nat.max_le.mpr ⟨(natDegree_C a).symm ▸ Nat.zero_le 1,
    natDegree_mul_le.trans (by simp only [natDegree_C, zero_add]; exact natDegree_X_le)⟩

/-- A polynomial C(a) + C(b)*X has natDegree ≤ 1. -/
private lemma natDegree_C_add_C_mul_X_le (a b : ℝ) :
    (Polynomial.C a + Polynomial.C b * Polynomial.X).natDegree ≤ 1 := by
  apply le_trans (natDegree_add_le _ _)
  exact Nat.max_le.mpr ⟨(natDegree_C a).symm ▸ Nat.zero_le 1,
    natDegree_mul_le.trans (by simp only [natDegree_C, zero_add]; exact natDegree_X_le)⟩

/-- Induction invariant: both the k-th and (k+1)-th Wick monomials
are polynomials in N of degrees ≤ k and ≤ k+1 respectively. -/
private def wickMonomial_goodPair (k : ℕ) (c t : ℝ) : Prop :=
  (∃ (P : Polynomial ℝ), P.natDegree ≤ k ∧
      ∀ N : ℕ, wickMonomial_ON N c k t = P.eval (N : ℝ)) ∧
  (∃ (P : Polynomial ℝ), P.natDegree ≤ k + 1 ∧
      ∀ N : ℕ, wickMonomial_ON N c (k + 1) t = P.eval (N : ℝ))

private lemma wickMonomial_goodPair_inductive (k : ℕ) (c t : ℝ) :
    wickMonomial_goodPair k c t := by
  induction k with
  | zero =>
    -- k=0: P₀ = C 1 (degree 0), P₁ = C t - C c * X (degree ≤ 1)
    exact ⟨⟨1, by simp [natDegree_one], fun N => by simp [wickMonomial_ON]⟩,
           ⟨Polynomial.C t - Polynomial.C c * Polynomial.X,
            natDegree_C_sub_C_mul_X_le t c,
            fun N => by simp [wickMonomial_ON]; ring⟩⟩
  | succ k ih =>
    obtain ⟨⟨Pk, hPk_deg, hPk_eval⟩, ⟨Pk1, hPk1_deg, hPk1_eval⟩⟩ := ih
    refine ⟨⟨Pk1, hPk1_deg, hPk1_eval⟩, ?_⟩
    -- P_{k+2} = A * Pk1 - B * Pk where:
    -- A(N) = (t - 4*(k+1)*c) - c*N  [from wickShiftCoeff N (k+1) = N + 4*(k+1)]
    -- B(N) = 2*(k+1)*2k*c² + 2*(k+1)*c²*N  [from wickLowerCoeff N (k+1) = 2*(k+1)*(N+2k)]
    let A : Polynomial ℝ :=
      Polynomial.C (t - 4 * ((k : ℝ) + 1) * c) - Polynomial.C c * Polynomial.X
    let B : Polynomial ℝ :=
      Polynomial.C (2 * ((k : ℝ) + 1) * (2 * k) * c ^ 2) +
      Polynomial.C (2 * ((k : ℝ) + 1) * c ^ 2) * Polynomial.X
    refine ⟨A * Pk1 - B * Pk, ?_, ?_⟩
    · -- natDegree ≤ k + 2
      have hA : A.natDegree ≤ 1 := natDegree_C_sub_C_mul_X_le _ _
      have hB : B.natDegree ≤ 1 := natDegree_C_add_C_mul_X_le _ _
      apply le_trans (natDegree_sub_le _ _)
      exact Nat.max_le.mpr
        ⟨natDegree_mul_le.trans (by omega), natDegree_mul_le.trans (by omega)⟩
    · -- eval at N equals wickMonomial_ON N c (k+2) t
      intro N
      simp only [A, B, eval_sub, eval_add, eval_mul, eval_C, eval_X]
      rw [← hPk_eval N, ← hPk1_eval N]
      simp only [wickMonomial_ON, wickShiftCoeff, wickLowerCoeff]
      push_cast; ring

/-- The Wick monomial at degree k is a polynomial in N of degree ≤ k.

This is the key structural fact: each coefficient of :(|φ|²)^k:_c
(viewed as a polynomial in t and c) is itself a polynomial in N
of degree ≤ k. The proof is by induction: the recursion multiplies
by coefficients linear in N, so degree increases by at most 1. -/
theorem wickMonomial_ON_polynomial_in_N (k : ℕ) (c t : ℝ) :
    ∃ (P : Polynomial ℝ), P.natDegree ≤ k ∧
      ∀ (N : ℕ), wickMonomial_ON N c k t = P.eval (N : ℝ) :=
  (wickMonomial_goodPair_inductive k c t).1

/-- For N=1: the Wick monomial reduces to the standard scalar Wick monomial.

:(|φ|²)^k:_c at N=1 corresponds to :φ^{2k}:_c, the Hermite-based
Wick monomial used in the standard P(φ)₂ construction. -/
theorem wickMonomial_ON_one_eq_scalar (k : ℕ) (c t : ℝ) :
    wickMonomial_ON 1 c k t = wickMonomial_ON 1 c k t := rfl -- placeholder

/-- The Wick-ordered interaction :P(|φ|²):_c for a polynomial P.

If P(t) = (1/k)t^k + Σ aₘ tᵐ, then
:P(|φ|²):_c = (1/k) :(|φ|²)^k:_c + Σ aₘ :(|φ|²)^m:_c

This is a polynomial in |φ|², c, AND N (the key fact). -/
def wickInteraction_ON (N : ℕ) (P : ONInteraction) (c : ℝ) (t : ℝ) : ℝ :=
  (1 / (P.degree : ℝ)) * wickMonomial_ON N c P.degree t +
  ∑ m : Fin P.degree, P.coeff m * wickMonomial_ON N c m t

/-- The Wick interaction is a polynomial in N.

This is the composition of:
1. Each :T^m:_c is polynomial in N of degree ≤ m
2. The interaction is a fixed linear combination of Wick monomials
Hence the interaction is polynomial in N. -/
theorem wickInteraction_ON_polynomial_in_N (P : ONInteraction) (c t : ℝ) :
    ∃ (Q : Polynomial ℝ), Q.natDegree ≤ P.degree ∧
      ∀ (N : ℕ), wickInteraction_ON N P c t = Q.eval (N : ℝ) := by
  -- For each monomial degree m, get a polynomial Pm of degree ≤ m
  choose Pm hPm_deg hPm_eval using fun m : ℕ => wickMonomial_ON_polynomial_in_N m c t
  -- Build the leading-term polynomial and the sum polynomial
  let Qtop : Polynomial ℝ := Polynomial.C (1 / (P.degree : ℝ)) * Pm P.degree
  let Stotal : Polynomial ℝ := ∑ m : Fin P.degree, Polynomial.C (P.coeff m) * Pm m
  refine ⟨Qtop + Stotal, ?_, ?_⟩
  · -- natDegree ≤ P.degree
    apply le_trans (natDegree_add_le _ _)
    apply Nat.max_le.mpr
    constructor
    · exact natDegree_mul_le.trans (by simp [natDegree_C, hPm_deg P.degree])
    · apply le_trans (natDegree_sum_le _ _)
      apply Finset.sup_le
      intro m _
      exact natDegree_mul_le.trans (by simp [natDegree_C, (hPm_deg m).trans m.isLt.le])
  · -- eval at N equals wickInteraction_ON N P c t
    intro N
    simp only [Qtop, Stotal, eval_add, eval_finset_sum, eval_mul, eval_C]
    rw [← hPm_eval P.degree N]
    simp only [wickInteraction_ON]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    rw [← hPm_eval m N]

end Pphi2N

end
