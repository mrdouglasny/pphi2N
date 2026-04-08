# pphi2N Status

**0 sorries, 12 axioms, 3194 jobs, 0 errors.**

## Main theorems (all proved, 0 sorries)

| Theorem | File | Statement |
|---------|------|-----------|
| `lsmTorusLimit_satisfies_OS` | ONTorusLimit.lean | O(N) LSM continuum limit on T²_L satisfies OS0+OS1+OS2 |
| `lsm_massGap_largeN` | LargeNMassGap.lean | Spectral gap m ≥ √(σ*/2) for N ≥ N₀ (finite volume) |
| `infiniteVolume_massGap_largeN` | InfiniteVolume.lean | Mass gap m > 0 in infinite volume for N ≥ N₀ |
| `infiniteVolume_massGap_allN` | InfiniteVolume.lean | Mass gap m > 0 in infinite volume for ALL N ≥ 1 (large λ) |

## pphi2N axioms (12)

### Continuum limit (6)

| # | Axiom | File | Difficulty | Proof strategy |
|---|-------|------|-----------|----------------|
| 1 | `latticeWickConstant` | LSMTorusMeasure:73 | Easy | Spectral sum Σ 1/(λ_k+m²), define concretely |
| 2 | `latticeWickConstant_pos` | LSMTorusMeasure:76 | Easy | Each term positive |
| 3 | `nComponentGreen_uniform_bound` | EmbeddingBound:73 | Medium | Port torusGreen_uniform_bound componentwise from gaussian-field |
| 4 | `lsmDensityTransferConstant` | ONTorusLimit:73 | Medium | Nelson bound exp(-V) ≤ exp(B), Jensen Z ≥ exp(-B') |
| 5 | `lsmGF_latticeApproximation_error_vanishes` | ONTorusLimit:724 | Medium | Port from pphi2 (fully proved there, ~130 lines) |
| 6 | `nComponentGFF_exp_moment_uniform` | ONTorusLimit:891 | Medium | Gaussian MGF E[exp(\|X\|)] ≤ 2exp(σ²/2) + Green bound |

### Mass gap — Hubbard-Stratonovich (2)

| # | Axiom | File | Difficulty | Proof strategy |
|---|-------|------|-----------|----------------|
| 7 | `sigma_measure_from_HS` | HubbardStratonovich:68 | Hard | Gaussian integration det(A)^{-N/2}, change of variables |
| 8 | `sigma_BL_variance_bound` | HubbardStratonovich:87 | Medium | Apply brascampLieb_poincare from markov-semigroups |

### Mass gap — spectral (2)

| # | Axiom | File | Difficulty | Proof strategy |
|---|-------|------|-----------|----------------|
| 9 | `conditionalSpectralGap` | TransferOperator:90 | Medium | -Δ+σ ≥ σ_min when σ ≥ σ_min (operator theory) |
| 10 | `sigma_correlation_exponential_decay` | InfiniteVolume:118 | Medium-Hard | Poincaré → semigroup decay (Bakry-Gentil-Ledoux §4.2) |

### Mass gap — infinite volume (2)

| # | Axiom | File | Difficulty | Proof strategy |
|---|-------|------|-----------|----------------|
| 11 | `phi_propagator_exponential_decay` | InfiniteVolume:152 | Hard | Resolvent perturbation for random Schrödinger |
| 12 | `randomSchrodinger_spectralGap` | InfiniteVolume:200 | Hard | Same, for any N ≥ 1 (no N threshold) |

## Dependency axioms

pphi2N imports from pphi2, gaussian-field, and markov-semigroups.
However, **none of the dependency axioms are in pphi2N's dependency chain.**

| Dependency | Axioms in repo | Axioms we use | What we import |
|-----------|---------------|--------------|----------------|
| pphi2 | 23 | **0** | `analyticOnNhd_integral` (proved theorem, 0 axioms) |
| gaussian-field | 9 | **0** | Configuration, GFF, torus embedding, Prokhorov (all proved) |
| markov-semigroups | 3 | **0** | BrascampLieb.lean imported but no theorems called |

**Total axioms pphi2N depends on: exactly 12 (all in pphi2N itself).**

The dependency repos' own axioms (23 + 9 + 3 = 35) are for OTHER
theorems in those repos that we don't use. The gaussian-field and pphi2
theorems we import are all fully proved.

## File inventory (20 Lean files)

| File | Lines | Axioms | Sorries | Key content |
|------|-------|--------|---------|-------------|
| Model/ONModel.lean | ~80 | 0 | 0 | O(N) model structure |
| Model/Interaction.lean | ~70 | 0 | 0 | O(N)-invariant polynomial |
| Model/LSM.lean | ~190 | 0 | 0 | LSM parameters, saddle point, gap equation |
| LatticeField/NComponentField.lean | ~60 | 0 | 0 | φ : Λ → ℝ^N, \|φ(x)\|² |
| LatticeField/ONGaussian.lean | ~100 | 0 | 0 | Wick constant, rising factorial (polynomial in N) |
| LatticeField/ProductGFF.lean | ~120 | 0 | 0 | Measure.pi, independence, marginal |
| LatticeField/ProductConfiguration.lean | ~80 | 0 | 0 | Configuration(Fin N → E) ≅ Fin N → Configuration E |
| WickOrdering/ONWick.lean | ~150 | 0 | 0 | Laguerre recursion, polynomial-in-N |
| SigmaMeasure/Basic.lean | ~160 | 0 | 0 | σ-field effective action |
| InteractingMeasure/ONLatticeAction.lean | ~90 | 0 | 0 | Lattice interaction V(φ) |
| InteractingMeasure/ONTorusMeasure.lean | ~340 | 0 | 0 | Boltzmann weight, probability measure, polynomial bounded below |
| InteractingMeasure/LatticeTranslation.lean | ~90 | 0 | 0 | V(T_v φ) = V(φ) via Fintype.sum_equiv |
| InteractingMeasure/DensityTransfer.lean | ~180 | 0 | 0 | Cauchy-Schwarz density transfer (Hölder p=q=2) |
| ContinuumLimit/NComponentTestFunction.lean | ~50 | 0 | 0 | NTP(TorusTestFunction, ℝ^N) |
| ContinuumLimit/NComponentEmbedding.lean | ~110 | 0 | 0 | Componentwise embedding + measurability |
| ContinuumLimit/EmbeddingBound.lean | ~90 | 1 | 0 | Uniform Green's function bound |
| ContinuumLimit/LSMTorusMeasure.lean | ~100 | 2 | 0 | LSM measure, Wick constant, probability instance |
| ContinuumLimit/ONTorusLimit.lean | ~950 | 3 | 0 | Tightness, Prokhorov, OS0-OS2, exp moments |
| MassGap/SigmaConcentration.lean | ~140 | 0 | 0 | σ-concentration, threshold, fluctuation bound |
| MassGap/HubbardStratonovich.lean | ~100 | 2 | 0 | HS transformation, σ-measure, BL variance |
| MassGap/TransferOperator.lean | ~150 | 1 | 0 | Conditional/unconditional spectral gap |
| MassGap/LargeNMassGap.lean | ~180 | 0 | 0 | Main mass gap theorem, explicit bounds |
| MassGap/InfiniteVolume.lean | ~250 | 3 | 0 | Poincaré → decay, random Schrödinger, all-N gap |
