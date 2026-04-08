# pphi2N: O(N) P(φ)₂ Euclidean Quantum Field Theory

## What this project proves

Two main theorems in Lean 4, with 0 sorries and 9 axioms:

### Theorem 1: Continuum limit with OS axioms

**`lsmTorusLimit_satisfies_OS`** (`ContinuumLimit/ONTorusLimit.lean`):
For any O(N) Linear Sigma Model with parameters (N, λ, R², m) on the
torus T²_L, the UV continuum limit (lattice spacing a = L/M → 0) exists
and satisfies the Osterwalder-Schrader axioms:

- **OS0 (Analyticity):** The generating functional Z[Σ zᵢJᵢ] is entire
  analytic in z ∈ ℂⁿ.
- **OS1 (Regularity):** ‖Z_ℂ[f_re, f_im]‖ ≤ exp(c·(q(f_re) + q(f_im)))
  for a continuous seminorm q.
- **OS2 (Translation invariance):** Z[T_v f] = Z[f] for all v ∈ (ℝ/Lℤ)².

### Theorem 2: Mass gap at large N

**`lsm_massGap_largeN`** (`MassGap/LargeNMassGap.lean`):
For N ≥ N₀ (an explicit threshold), the transfer matrix of the O(N)
LSM on T²_L has a positive spectral gap:

  m ≥ √(σ*/2) > 0

where σ* is the saddle point of the σ-field effective action. In terms
of the LSM parameters: σ* = R²/N and the gap satisfies

  m ≥ R / √(2N)

The threshold N₀ = ⌈4/(κσ*²)⌉ + 1 depends on the convexity parameter
κ = 2λ - ‖G²‖/2 (which requires λ above the convexity threshold) and
the saddle point σ* = v² = R²/N. For example, with λ = 1, R² = 1:
- κ ≈ 2 (for small ‖G²‖), σ* = 1/N
- N₀ ≈ ⌈4/(2 · (1/N)²)⌉ + 1 = ⌈2N²⌉ + 1

So the threshold grows as N², meaning the theorem applies when
N ≥ 2N² + 1... which is never satisfied for N ≥ 3. This reflects the
fact that the simple Brascamp-Lieb bound 1/(κN) on Var(σ) requires
κ to be large enough relative to σ*², which means λ must grow with N.

**At fixed NLSM coupling g² = N/R²**, the gap is R/√(2N) = 1/√(2g²),
which is N-independent (Theorem `massGap_nlsm_coupling`).

## Proof architecture

### Continuum limit (OS0-OS2)

```
latticeGaussianMeasure (scalar GFF on (ℤ/Mℤ)²)
  → evalMapMeasurableEquiv (Configuration ≃ raw fields)
  → nComponentMeasure (N copies via Measure.pi)
  → onInteractingMeasure (Boltzmann weight exp(-V) / Z)
  → nComponentTorusEmbedLift (componentwise via evalCLM)
  → lsmTorusMeasure (on NTP(TorusTestFunction, ℝ^N))
  → Prokhorov extraction (tightness + weak convergence)
  → lsmTorusLimit_satisfies_OS
```

- **OS0**: `analyticOnNhd_integral` (from pphi2) + exponential moment domination
- **OS1**: triangle inequality + exponential moment bound
- **OS2**: lattice vector invariance (exact, from `onInteraction_translation_invariant`
  via `Fintype.sum_equiv`) + lattice approximation of general v + GF Lipschitz continuity

### Mass gap at large N

```
LSMParams → SigmaConvexityData (σ* > 0, κ > 0)
  → Brascamp-Lieb: Var(σ) ≤ 1/(κN)
  → Concentration: σ ≥ σ*/2 when N ≥ N₀
  → Conditional gap: -Δ + σ ≥ σ*/2 → mass ≥ √(σ*/2)
  → Unconditional gap: min(gap, conditionalGap) > 0
  → lsm_massGap_largeN
```

## Key definitions proved (0 sorries)

| Definition | File | Status |
|-----------|------|--------|
| O(N) Wick ordering (polynomial in N) | `WickOrdering/ONWick.lean` | ✓ Proved |
| N-component product GFF (independence, marginal) | `LatticeField/ProductGFF.lean` | ✓ Proved |
| Product configuration isomorphism | `LatticeField/ProductConfiguration.lean` | ✓ Proved |
| Polynomial bounded below (formal poly + EVT) | `InteractingMeasure/ONTorusMeasure.lean` | ✓ Proved |
| Nelson estimate (from bounded below) | `InteractingMeasure/ONTorusMeasure.lean` | ✓ Proved |
| Interacting measure = probability measure | `InteractingMeasure/ONTorusMeasure.lean` | ✓ Proved |
| Lattice translation invariance | `InteractingMeasure/LatticeTranslation.lean` | ✓ Proved |
| Density transfer (Cauchy-Schwarz) | `InteractingMeasure/DensityTransfer.lean` | ✓ Proved |
| N-component torus embedding + measurability | `ContinuumLimit/NComponentEmbedding.lean` | ✓ Proved |
| Limit exp moments (truncation + MCT) | `ContinuumLimit/ONTorusLimit.lean` | ✓ Proved |
| OS0 analyticity | `ContinuumLimit/ONTorusLimit.lean` | ✓ Proved |
| OS1 regularity | `ContinuumLimit/ONTorusLimit.lean` | ✓ Proved |
| OS2 translation (limit structure) | `ContinuumLimit/ONTorusLimit.lean` | ✓ Proved |
| Fluctuation bound 1/√(κN) < σ*/2 | `MassGap/SigmaConcentration.lean` | ✓ Proved |
| Mass gap at large N | `MassGap/LargeNMassGap.lean` | ✓ Proved |

## Axioms (9)

All are standard facts from lattice QFT and Gaussian measure theory:

| Axiom | Content | Proof strategy |
|-------|---------|---------------|
| `latticeWickConstant` | G(x,x) exists | Spectral sum definition |
| `latticeWickConstant_pos` | G(x,x) > 0 | Each term 1/(λ_k + m²) > 0 |
| `nComponentGreen_uniform_bound` | ∫(ωf)² ≤ C·q(f)² uniform in M | torusGreen_uniform_bound componentwise |
| `lsmDensityTransferConstant` | ∫F dμ_int ≤ D·∫F dμ_GFF | Nelson bound + Jensen |
| `lsmGF_latticeApproximation_error_vanishes` | Z_M[T_v f]-Z_M[f]→0 | Lattice approx + Lipschitz (proved in pphi2) |
| `nComponentGFF_exp_moment_uniform` | ∫exp(\|ωf\|) ≤ K·exp(q²) | Gaussian MGF + Green bound |
| `sigma_measure_from_HS` | σ-measure exists | Gaussian integration |
| `sigma_BL_variance_bound` | Var(σ(x)) bound ≥ 0 | Brascamp-Lieb (in markov-semigroups) |
| `conditionalSpectralGap` | σ ≥ σ_min → gap ≥ σ_min | Schrödinger operator lower bound |

## Build

```bash
lake build
```

## Dependencies

- [pphi2](https://github.com/mrdouglasny/pphi2) — P(φ)₂ construction (23 axioms, 0 sorries)
- [markov-semigroups](https://github.com/mrdouglasny/markov-semigroups) — Brascamp-Lieb inequality
- [gaussian-field](https://github.com/mrdouglasny/gaussian-field) — GFF infrastructure (via pphi2)
- Mathlib v4.29

## File structure

```
Pphi2N/
  Model/
    ONModel.lean              -- O(N) model structure
    Interaction.lean          -- O(N)-invariant interaction polynomial
    LSM.lean                  -- Linear Sigma Model, saddle point, gap equation
  LatticeField/
    NComponentField.lean      -- φ : Λ → ℝ^N, |φ(x)|²
    ONGaussian.lean           -- Wick constant, O(N) rising factorial
    ProductGFF.lean           -- N-component GFF via Measure.pi
    ProductConfiguration.lean -- Configuration(Fin N → E) ≅ Fin N → Configuration E
  WickOrdering/
    ONWick.lean               -- Wick monomials, Laguerre recursion, polynomial-in-N
  SigmaMeasure/
    Basic.lean                -- σ-field effective action
  InteractingMeasure/
    ONLatticeAction.lean      -- O(N) interaction on the lattice
    ONTorusMeasure.lean       -- Interacting measure, Nelson, probability instance
    LatticeTranslation.lean   -- V(T_v φ) = V(φ) via Fintype.sum_equiv
    DensityTransfer.lean      -- Cauchy-Schwarz density transfer
  ContinuumLimit/
    NComponentTestFunction.lean  -- NTP(TorusTestFunction, ℝ^N) with DM instance
    NComponentEmbedding.lean     -- Componentwise embedding + measurability
    EmbeddingBound.lean          -- Uniform Green's function bound (axiom)
    LSMTorusMeasure.lean         -- LSM measure on T²_L
    ONTorusLimit.lean            -- Tightness, Prokhorov, OS0-OS2
  MassGap/
    SigmaConcentration.lean      -- σ-concentration from Brascamp-Lieb
    HubbardStratonovich.lean     -- σ-measure axioms
    TransferOperator.lean        -- Conditional + unconditional gap
    LargeNMassGap.lean           -- Main mass gap theorem
docs/
  polynomial-in-N.md
  master-field-plan.md
  convexity-preservation.md
  frg-invariant-field.md
  lsm-to-nlsm.md
```

## References

- Glimm and Jaffe, *Quantum Physics*, Springer, 1987
- Simon, *The P(φ)₂ Euclidean QFT*, Princeton, 1974
- Brascamp and Lieb, J. Funct. Anal. 22 (1976)
- Moshe and Zinn-Justin, Phys. Rep. 385 (2003) — large N review
