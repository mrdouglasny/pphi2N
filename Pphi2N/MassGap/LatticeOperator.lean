/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lattice Laplacian and Positive Semidefiniteness

Proves the lattice Laplacian is positive semidefinite using Mathlib's
`SimpleGraph.posSemidef_lapMatrix`, and derives the conditional spectral
gap: when σ(x) ≥ c > 0, the operator -Δ + σ has gap ≥ c.

## Main results

- `laplacian_nonneg_general` — v^T L v ≥ 0 for any graph Laplacian L
- `psd_add_scalar_bound` — H PSD + c > 0 → v^T(H+cI)v ≥ c·‖v‖²

## References

- Mathlib: `SimpleGraph.posSemidef_lapMatrix`
- Reed-Simon, *Methods of Modern Mathematical Physics IV*, Ch. XIII
-/

import Mathlib.Combinatorics.SimpleGraph.LapMatrix

noncomputable section

open Finset Matrix SimpleGraph

namespace Pphi2N

/-! ## Laplacian positive semidefiniteness

The Laplacian of ANY simple graph is positive semidefinite (Mathlib).
For ℝ: `star x = x` (TrivialStar), so v^T L v = v ⬝ᵥ (L *ᵥ v) ≥ 0. -/

/-- **The graph Laplacian is nonneg-definite: v^T L v ≥ 0.**

For ANY finite graph G, the Laplacian L = D - A satisfies
v ⬝ᵥ (L *ᵥ v) ≥ 0 for all vectors v. Equivalently:

  v^T L v = ½ Σ_{i~j} (vᵢ - vⱼ)² ≥ 0

This is the key ingredient for: -Δ + σ ≥ σ when σ ≥ 0. -/
theorem laplacian_nonneg_general {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V → ℝ) :
    0 ≤ v ⬝ᵥ (G.lapMatrix ℝ) *ᵥ v := by
  have h := @posSemidef_lapMatrix V ℝ _ G _ _ _ _ _ _ _
  have hv := h.dotProduct_mulVec_nonneg v
  simp [star_trivial] at hv
  exact hv

/-! ## Consequence: -Δ + c has spectral gap c

When the Laplacian L ≥ 0 (PSD), adding a constant c > 0 gives:
  ⟨v, (L + c·I)v⟩ ≥ c · ⟨v, v⟩

So all eigenvalues of L + c·I are ≥ c. This is the "conditional
spectral gap" for -Δ + σ when σ(x) ≥ c for all x. -/

/-- For a PSD matrix H and scalar c > 0: ⟨v, (H + c·I)v⟩ ≥ c·⟨v,v⟩.

This means spectrum(H + c·I) ⊂ [c, ∞). -/
theorem psd_add_scalar_bound {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℝ) (hH : PosSemidef H) (c : ℝ) (hc : 0 < c) (v : n → ℝ) :
    c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (H + c • (1 : Matrix n n ℝ)) *ᵥ v := by
  simp only [Matrix.add_mulVec, dotProduct_add, smul_mulVec, Matrix.one_mulVec]
  have h1 : 0 ≤ v ⬝ᵥ H *ᵥ v := by
    have := hH.dotProduct_mulVec_nonneg v
    simp [star_trivial] at this
    exact this
  have h2 : v ⬝ᵥ (c • v) = c * (v ⬝ᵥ v) := by
    unfold dotProduct
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl fun x _ => show v x * (c * v x) = c * (v x * v x) by ring]
    exact (Finset.mul_sum _ _ _).symm
  linarith

end Pphi2N

end
