/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# O(N)-Invariant Interaction Polynomials

An O(N)-invariant interaction is P(|φ|²) where P is a polynomial in one
real variable t = |φ|². For N=1, |φ|² = φ² and P(φ²) recovers the
standard P(φ)₂ interaction.

## Main definitions

- `ONInteraction` — polynomial P(t) with P bounded below (leading coeff > 0,
  even degree ≥ 2 in t, i.e., degree ≥ 4 in the fields)

## Examples

- P(t) = λt²: the (|φ|⁴)₂ model (quartic in fields)
- P(t) = λt² + μt: quartic + mass correction
- P(t) = λt³: sextic in fields (degree 6)

## References

- Simon, *The P(φ)₂ Euclidean QFT*, §II.3
- Glimm-Jaffe, *Quantum Physics*, §6.1
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Order.Compact

noncomputable section

namespace Pphi2N

/-- An O(N)-invariant interaction polynomial P(t).

The interaction functional is V(φ) = ∫ :P(|φ(x)|²):_c dx where
|φ|² = Σᵢ (φⁱ)² is the O(N)-invariant squared norm.

P(t) is a polynomial in the single variable t = |φ|², so degree k
in t corresponds to degree 2k in the fields. We require:
- degree ≥ 2 (quartic or higher in fields)
- positive leading coefficient (bounded below)

For N=1: |φ|² = φ², so P(|φ|²) = P(φ²). If P(t) = λt², then
V = λ ∫ :φ⁴: dx, which is the standard P(φ)₂ quartic interaction. -/
structure ONInteraction where
  /-- Degree k ≥ 2 in t = |φ|² (= degree 2k ≥ 4 in the fields). -/
  degree : ℕ
  hdeg : 2 ≤ degree
  /-- Coefficients a₀, ..., a_{k-1}. The leading coefficient a_k = 1/k
  (normalized so P(t) = (1/k)t^k + lower terms). -/
  coeff : Fin degree → ℝ
  /-- Constant coefficient is nonpositive (vacuum energy). -/
  coeff_zero_nonpos : coeff ⟨0, by omega⟩ ≤ 0

/-- Evaluate P(t) = (1/k)t^k + Σ_{m<k} aₘ tᵐ. -/
def ONInteraction.eval (P : ONInteraction) (t : ℝ) : ℝ :=
  (1 / (P.degree : ℝ)) * t ^ P.degree + ∑ m : Fin P.degree, P.coeff m * t ^ (m : ℕ)

/-- P is bounded below on [0, ∞) (the physical domain: t = |φ|² ≥ 0).

P(t) = (1/k)t^k + lower terms with k ≥ 2 and leading coeff > 0.
For t ≥ 0: the leading term grows as t^k → +∞, dominating lower terms.
The minimum on [0, ∞) exists and is finite. -/
theorem ONInteraction.bounded_below_nonneg (P : ONInteraction) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → C ≤ P.eval t := by
  -- Build a formal Polynomial ℝ whose eval agrees with P.eval
  have hdeg_pos : 0 < P.degree := by linarith [P.hdeg]
  have h1k_ne : (1 / (P.degree : ℝ)) ≠ 0 :=
    one_div_ne_zero (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hdeg_pos))
  -- The formal polynomial
  set Q : Polynomial ℝ :=
    Polynomial.C (1 / (P.degree : ℝ)) * Polynomial.X ^ P.degree +
    ∑ m : Fin P.degree, Polynomial.C (P.coeff m) * Polynomial.X ^ (m : ℕ) with hQ_def
  -- Q evaluates to P.eval
  have hQ_eval : ∀ t : ℝ, Q.eval t = P.eval t := by
    intro t
    simp only [hQ_def, ONInteraction.eval, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_finset_sum]
  -- natDegree of the two summands
  have hlead_nd : (Polynomial.C (1 / (P.degree : ℝ)) * Polynomial.X ^ P.degree).natDegree
      = P.degree :=
    Polynomial.natDegree_C_mul_X_pow P.degree _ h1k_ne
  have hsum_nd : (∑ m : Fin P.degree, Polynomial.C (P.coeff m) *
      Polynomial.X ^ (m : ℕ)).natDegree < P.degree := by
    apply lt_of_le_of_lt
    · apply Polynomial.natDegree_sum_le_of_forall_le (n := P.degree - 1)
      intro m _
      calc (Polynomial.C (P.coeff m) * Polynomial.X ^ (m : ℕ)).natDegree
          ≤ (Polynomial.C (P.coeff m)).natDegree + (Polynomial.X ^ (m : ℕ)).natDegree :=
            Polynomial.natDegree_mul_le
        _ = 0 + m.val := by rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
        _ = m.val := zero_add _
        _ ≤ P.degree - 1 := by omega
    · omega
  -- Q.natDegree = P.degree
  have hQ_nd : Q.natDegree = P.degree := by
    rw [hQ_def, Polynomial.natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead_nd]), hlead_nd]
  -- Q has positive leading coefficient 1/P.degree
  have hQ_lc : 0 < Q.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hQ_nd, hQ_def, Polynomial.coeff_add,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one,
      Polynomial.coeff_eq_zero_of_natDegree_lt hsum_nd, add_zero]
    exact div_pos one_pos (Nat.cast_pos.mpr hdeg_pos)
  -- Q ≠ 0
  have hQ_ne : Q ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mp (ne_of_gt hQ_lc)
  -- Q → +∞ as t → +∞
  have hQ_tendsto : Filter.Tendsto (fun t : ℝ => Q.eval t) Filter.atTop Filter.atTop :=
    Q.tendsto_atTop_of_leadingCoeff_nonneg
      (by rw [Polynomial.degree_eq_natDegree hQ_ne, hQ_nd]; exact_mod_cast hdeg_pos)
      (le_of_lt hQ_lc)
  -- P.eval is continuous on Ici 0
  have hcont : ContinuousOn (fun t : ℝ => P.eval t) (Set.Ici 0) := by
    unfold ONInteraction.eval
    apply Continuous.continuousOn
    exact (continuous_const.mul (continuous_pow _)).add
      (continuous_finset_sum _ (fun m _ => continuous_const.mul (continuous_pow _)))
  -- Q.eval is eventually ≥ Q.eval 0 outside compact set, restricted to Ici 0
  have h_large : ∀ᶠ t in Filter.cocompact ℝ ⊓ Filter.principal (Set.Ici 0),
      Q.eval 0 ≤ Q.eval t := by
    rw [cocompact_eq_atBot_atTop, inf_sup_right,
        (Filter.disjoint_atBot_principal_Ici (0 : ℝ)).eq_bot, bot_sup_eq]
    exact (hQ_tendsto.eventually (Filter.eventually_ge_atTop (Q.eval 0))).filter_mono inf_le_left
  -- h_large in terms of P.eval
  have h_large' : ∀ᶠ t in Filter.cocompact ℝ ⊓ Filter.principal (Set.Ici 0),
      P.eval 0 ≤ P.eval t := by
    apply h_large.mono; intro t ht
    rwa [hQ_eval, hQ_eval] at ht
  -- EVT: P.eval has a minimum t₀ on Ici 0
  obtain ⟨t₀, _ht₀_mem, ht₀_min⟩ :=
    hcont.exists_isMinOn' isClosed_Ici (Set.mem_Ici.mpr le_rfl) h_large'
  exact ⟨P.eval t₀, fun t ht => ht₀_min (Set.mem_Ici.mpr ht)⟩

/-- The quartic interaction P(t) = λt² (φ⁴ model). -/
def quarticInteraction (lam : ℝ) (hlam : 0 < lam) : ONInteraction where
  degree := 2
  hdeg := le_refl 2
  coeff := fun m => 0  -- no lower-order terms; leading = 1/2
  coeff_zero_nonpos := le_refl 0

end Pphi2N

end
