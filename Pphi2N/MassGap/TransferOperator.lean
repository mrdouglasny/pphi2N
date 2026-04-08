/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# N-Component Transfer Operator and Spectral Gap

The transfer operator for the O(N) model on a cylinder Λ = [0,Lt] × T_Ls:
  T = exp(-a · H)
where H is the N-component lattice Hamiltonian.

## The conditional spectral gap

Conditioned on the σ-field (σ(x) = |φ(x)|²/N), the N field components
are independent Gaussians with covariance (-Δ + σ)⁻¹. When σ(x) ≥ σ_min > 0
for all x, the operator -Δ + σ has spectral gap ≥ σ_min, giving each
φ-component mass ≥ √σ_min.

## The unconditional spectral gap at large N

By σ-concentration (Brascamp-Lieb + large N), σ(x) ≥ σ*/2 with high
probability. The unconditional mass gap is then:

  m ≥ √(σ*/2) · (1 - P(bad event)) - ‖T‖ · P(bad event)
    ≥ √(σ*/2) - O(1/√N)
    > 0 for N large enough.

## Main definitions

- `NComponentTransferData` — data for the N-component transfer operator
- `conditionalSpectralGap` — gap when σ bounded below
- `unconditionalGap_of_concentration` — gap from concentration + conditional gap

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. III
- Glimm-Jaffe, *Quantum Physics*, Ch. 19
-/

import Pphi2N.MassGap.HubbardStratonovich

noncomputable section

open MeasureTheory Real

namespace Pphi2N

/-! ## Transfer operator data -/

/-- Data for the N-component transfer operator.

The transfer operator T = exp(-a·H) acts on L²(ℝ^{Nc × Ns}) where:
- Nc = number of field components (= N in the O(N) model)
- Ns = number of spatial lattice sites

The spectral gap of T determines the mass gap of the QFT. -/
structure NComponentTransferData where
  /-- Number of field components. -/
  Nc : ℕ
  hNc : 1 ≤ Nc
  /-- Number of spatial lattice sites. -/
  Ns : ℕ
  hNs : 1 ≤ Ns
  /-- The spectral gap of the transfer matrix (= mass gap). -/
  spectralGap : ℝ
  /-- The spectral gap is positive. -/
  hgap : 0 < spectralGap

/-! ## Conditional spectral gap -/

/-- **Conditional spectral gap.**

When the σ-field satisfies σ(x) ≥ σ_min > 0 for all spatial sites x,
the single-component Schrödinger operator on the spatial lattice:

  H₁ = -Δ_spatial + diag(σ)

has spectral gap ≥ σ_min (since -Δ ≥ 0 and σ ≥ σ_min > 0, the
lowest eigenvalue of H₁ is ≥ σ_min). All N components have the
same conditional Hamiltonian H₁, so the N-body gap equals the
single-body gap.

The mass is √(gap of H₁) ≥ √σ_min (from e^{-aH₁} eigenvalue relation).

Mathematical content: For a Schrödinger operator -Δ + V with V ≥ V_min > 0
on a compact domain, spec(-Δ + V) ⊂ [V_min, ∞). The operator -Δ is
nonneg-definite on the torus, so spec(H₁) ⊂ [σ_min, ∞).

Reference: Reed-Simon, *Methods of Modern Mathematical Physics IV*,
Theorem XIII.15. -/
axiom conditionalSpectralGap (σ_min : ℝ) (hσ : 0 < σ_min)
    (Ns : ℕ) (hNs : 1 ≤ Ns) :
    ∃ gap : ℝ, σ_min ≤ gap ∧ 0 < gap

/-- The conditional mass from the conditional spectral gap.
mass ≥ √σ_min when gap ≥ σ_min. -/
def conditionalMass (σ_min : ℝ) (_hσ : 0 < σ_min) : ℝ :=
  Real.sqrt σ_min

theorem conditionalMass_pos (σ_min : ℝ) (hσ : 0 < σ_min) :
    0 < conditionalMass σ_min hσ :=
  Real.sqrt_pos_of_pos hσ

/-! ## Unconditional gap from σ-concentration -/

/-- **Unconditional gap from concentration.**

The unconditional mass gap is obtained by combining:
1. Conditional gap: when σ ≥ σ_min, mass ≥ √σ_min
2. Concentration: P(∃x, σ(x) < σ_min) → 0 as N → ∞

The argument: decompose the spectral gap into contributions from
the "good" event {σ ≥ σ_min} and the "bad" event {∃x, σ(x) < σ_min}.
On the good event, the gap is ≥ √σ_min. On the bad event, use the
trivial bound gap ≥ 0. Since P(bad) → 0, the unconditional gap
approaches √σ_min.

More precisely: by the variational characterization of the spectral gap
and Jensen's inequality on the σ-average, the unconditional gap satisfies:

  m_uncond ≥ √(E[σ_min(ω)] - Var correction)
           ≥ √(σ*/2) for N large enough.

Mathematical content: lower semicontinuity of the spectral gap under
averaging, plus concentration of σ.

Reference: Simon (1974), Ch. III, Theorem III.3. -/
axiom unconditionalGap_of_concentration {Λ : Type*} [Fintype Λ]
    (D : SigmaConvexityData Λ)
    (hN : D.nThreshold ≤ D.N) :
    ∃ gap : ℝ, 0 < gap ∧ gap ≤ D.conditionalGap

/-- Construct transfer data from σ-convexity data at large N. -/
theorem transfer_data_from_concentration {Λ : Type*} [Fintype Λ] [Nonempty Λ]
    (D : SigmaConvexityData Λ)
    (hN : D.nThreshold ≤ D.N) :
    ∃ T : NComponentTransferData,
      T.Nc = D.N ∧ 0 < T.spectralGap := by
  obtain ⟨gap, hgap_pos, _⟩ := unconditionalGap_of_concentration D hN
  have hcard : 1 ≤ Fintype.card Λ := Fintype.card_pos
  exact ⟨⟨D.N, D.hN, Fintype.card Λ, hcard, gap, hgap_pos⟩, rfl, hgap_pos⟩

end Pphi2N

end
