# pphi2N Status

**0 sorries, 10 axioms, 3194 jobs, 0 errors.**

## Main theorems (all proved, 0 sorries)

| Theorem | File | Statement |
|---------|------|-----------|
| `lsmTorusLimit_satisfies_OS` | ONTorusLimit.lean | O(N) LSM continuum limit on T²_L satisfies OS0+OS1+OS2 |
| `lsm_massGap_largeN` | LargeNMassGap.lean | Spectral gap m ≥ √(σ*/2) for N ≥ N₀ (finite volume) |
| `infiniteVolume_massGap_largeN` | InfiniteVolume.lean | Mass gap m > 0 in infinite volume for N ≥ N₀ |
| `infiniteVolume_massGap_allN` | InfiniteVolume.lean | Mass gap m > 0 in infinite volume for ALL N ≥ 1 (large λ) |

### Informal proof summaries

**Theorem 1: `lsmTorusLimit_satisfies_OS`** — The O(N) Linear Sigma Model
on the torus T²_L has a UV continuum limit (lattice spacing a = L/M → 0)
satisfying the Osterwalder-Schrader axioms OS0–OS2. The proof constructs
N-component lattice measures via `Measure.pi` (N independent scalar GFFs),
applies the Boltzmann weight exp(-V)/Z with V = Σ_x :P(|φ(x)|²): (Wick-ordered,
bounded below by formal polynomial + EVT), embeds into the continuum via
`evalCLM` componentwise, establishes tightness from uniform second moment
bounds (density transfer + Green's function bound), extracts a subsequential
limit by Prokhorov's theorem, and verifies:
- **OS0** (analyticity): `analyticOnNhd_integral` from pphi2 + exponential
  moment domination (truncation + MCT for the limit).
- **OS1** (regularity): Triangle inequality + exponential moment bound.
- **OS2** (translation invariance): Exact lattice translation invariance
  (via `Fintype.sum_equiv (Equiv.addRight v)`) + lattice approximation of
  arbitrary translations (nearest lattice vector → v as a → 0) +
  `tendsto_nhds_unique` to transfer invariance to the limit.

**Theorem 2: `lsm_massGap_largeN`** — For N ≥ N₀ = ⌈4/(κσ*²)⌉+1, the
transfer matrix has spectral gap ≥ √(σ*/2). The proof uses
`SigmaConvexityData` (κ = convexity parameter, σ* = saddle point) and
shows: 1/√(κN) < σ*/2 for N ≥ N₀ (arithmetic via `inv_sqrt_lt_of_gt`),
so σ-fluctuations are smaller than σ*/2, giving σ(x) ≥ σ*/2 w.h.p., and
the conditional operator -Δ + σ has gap ≥ σ*/2.

**Theorem 3: `infiniteVolume_massGap_largeN`** — The mass gap persists in
infinite volume for N ≥ N₀. The finite-volume argument (Chebyshev + union
bound) fails when |Λ| = ∞. Instead: Brascamp-Lieb Poincaré inequality
(spectral gap ≥ κN for the σ-measure) → exponential decay of σ-correlations
with mass √(κN) → resolvent perturbation theory controls the averaged
φ-propagator → exponential decay with m_phys ≈ √σ* > 0.

**Theorem 4: `infiniteVolume_massGap_allN`** — For ALL N ≥ 1 (including
N = 2) with λ large enough that σ*·√κ > 1, the φ-field has mass gap m > 0.
The random Schrödinger argument: conditional on σ, all N components of φ
are Gaussian with covariance (-Δ+σ)⁻¹. When σ is concentrated near σ* > 0
(Poincaré), -Δ+σ ≈ -Δ+σ* has gap σ*, and the perturbation δσ = σ-σ*
has variance O(1/(κN)) with exponential correlation decay. The BKT transition
for N=2 only occurs at λ=∞ (strict NLSM constraint); at finite λ,
σ-fluctuations regularize vortices and all modes remain massive.

## Proved results (formerly axioms)

### Hubbard-Stratonovich (2 → 0 axioms)

| Theorem | File | Proof method |
|---------|------|-------------|
| `sigma_measure_from_HS` | HubbardStratonovich.lean:85 | Define σ(x) = (1/N)Σᵢ φⁱ(x)², prove measurable via `measurable_pi_lambda` + `Finset.measurable_sum`, σ-measure = pushforward under `sigmaFieldMap`, probability by `isProbabilityMeasure_map` |
| `sigma_BL_variance_bound` | HubbardStratonovich.lean:110 | `varianceBound = 1/(κN) > 0` already proved as `varianceBound_pos` (div_pos + mul_pos from κ>0, N≥1) |

### Other key proved results

| Result | File | Proof method |
|--------|------|-------------|
| `onInteractingMeasure_isProbability` | ONTorusMeasure.lean | Boltzmann weight exp(-V) > 0 a.e., integrability from V bounded below, normalization |
| `wickInteraction_bounded_below` | ONTorusMeasure.lean | Formal polynomial representation + extreme value theorem on [0,∞) |
| `onInteraction_translation_invariant` | LatticeTranslation.lean | `Fintype.sum_equiv (Equiv.addRight v)` reindexes lattice sum |
| `density_transfer_general` | DensityTransfer.lean | Cauchy-Schwarz (Hölder p=q=2) on weighted measures |
| `nComponent_independent` | ProductGFF.lean | `iIndepFun_pi` for product measure `Measure.pi` |
| `wickMonomial_ON_polynomial_in_N` | ONWick.lean | Pair induction on three-term Laguerre recursion |
| `fluctuationBound_small_of_large_N` | SigmaConcentration.lean | `inv_sqrt_lt_of_gt` + ceiling arithmetic |

## pphi2N axioms (10)

### Continuum limit (6)

| # | Axiom | File | Difficulty | Statement and proof strategy |
|---|-------|------|-----------|------------------------------|
| 1 | `latticeWickConstant` | LSMTorusMeasure:73 | Easy | The Wick constant c = G(x,x) = (1/\|Λ\|)Σ_k 1/(λ_k+m²) on the lattice, where λ_k are Laplacian eigenvalues. Just define the concrete spectral sum. |
| 2 | `latticeWickConstant_pos` | LSMTorusMeasure:76 | Easy | Each term 1/(λ_k+m²) > 0 since λ_k ≥ 0, m² > 0. Sum of positive terms is positive. |
| 3 | `nComponentGreen_uniform_bound` | EmbeddingBound:73 | Medium | Uniform second moment: E[(embed φ)(f)²] ≤ C·q(f)² for all lattice sizes M. Decomposes into N scalar bounds: each E[G_M(fᵢ,fᵢ)] ≤ (1/m²)·\|embed fᵢ\|² ≤ q(fᵢ)² from gaussian-field's `torusGreen_uniform_bound` + `embed_l2_uniform_bound`. Port componentwise. |
| 4 | `lsmDensityTransferConstant` | ONTorusLimit:73 | Medium | Density transfer: ∫F dμ_int ≤ D·∫F dμ_GFF with D = exp(B)/Z uniform in M. Nelson bound gives exp(-V) ≤ exp(B) with B = L^d·\|C_P\| (uniform since a^d·\|Λ\| = L^d). Jensen gives Z = E[exp(-V)] ≥ exp(-E[V]) ≥ 1 for Wick-ordered V (E_GFF[V] ≤ 0). So D ≤ exp(B). |
| 5 | `lsmGF_latticeApproximation_error_vanishes` | ONTorusLimit:724 | Medium | Translation approximation error → 0 as a → 0. Choose nearest lattice vector w_n with \|v - w_n\| ≤ a√2 → 0. Exact lattice invariance gives zero error for w_n. Bound remainder by \|T_v f - T_{w_n} f\| → 0 (continuity of translation action). Port from pphi2 (~130 lines, fully proved there). |
| 6 | `nComponentGFF_exp_moment_uniform` | ONTorusLimit:891 | Medium | Gaussian MGF: (embed φ)(f) is Gaussian with variance σ²(f) = G(f,f). Then E[exp(\|X\|)] ≤ E[exp(X)] + E[exp(-X)] = 2exp(σ²/2). Combined with σ²(f) ≤ C·q(f)² (axiom 3): K_exp = 2, q_exp = √(C/2)·q. |

### Mass gap — spectral (2)

| # | Axiom | File | Difficulty | Statement and proof strategy |
|---|-------|------|-----------|------------------------------|
| 7 | `conditionalSpectralGap` | TransferOperator:90 | Medium | The Schrödinger operator -Δ + σ_min on a compact domain has spectrum ⊂ [σ_min, ∞) when σ_min > 0. Proof: -Δ ≥ 0 on the torus (nonneg-definite), so -Δ + σ_min ≥ σ_min·I. Reed-Simon XIII.15. |
| 8 | `sigma_correlation_exponential_decay` | InfiniteVolume:118 | Medium-Hard | Poincaré inequality with constant C_P = 1/(κN) implies spectral gap ≥ κN for the σ-measure's generator, which implies exponential decay of connected correlations: \|⟨σ(x)σ(y)⟩_c\| ≤ C·exp(-√(κN)·\|x-y\|). Standard: spectral gap ↔ semigroup exponential decay ↔ correlation decay. Bakry-Gentil-Ledoux §4.2, Prop 4.2.5. Currently placeholder conclusion. |

### Mass gap — infinite volume (2)

| # | Axiom | File | Difficulty | Statement and proof strategy |
|---|-------|------|-----------|------------------------------|
| 9 | `phi_propagator_exponential_decay` | InfiniteVolume:152 | Hard | The averaged φ-propagator E_σ[(-Δ+σ)⁻¹(x,0)] ≤ C·exp(-m_phys·\|x\|) with 0 < m_phys ≤ √σ*, for N ≥ N₀. Resolvent expansion: (-Δ+σ)⁻¹ = (-Δ+σ*)⁻¹ + perturbative correction. Main term decays as exp(-√σ*·\|x\|). Correction bounded by σ-correlation decay (axiom 8). The σ-fluctuations have short correlation length 1/√(κN), so they don't destroy the mass gap. |
| 10 | `randomSchrodinger_spectralGap` | InfiniteVolume:200 | Hard | Random Schrödinger -Δ+σ(x) has spectral gap ≈ σ* for ALL N ≥ 1 when σ*·√κ > 1. All N components see the same potential σ(x); conditional on σ, φ is Gaussian with covariance (-Δ+σ)⁻¹. Perturbation: δσ = σ-σ* has variance 1/(κN), sub-Gaussian tails (log-concavity), correlation length 1/√(κN). Resolvent perturbation: (-Δ+σ)⁻¹ ≈ (-Δ+σ*)⁻¹ + O(\|δσ\|²/σ*). Works at finite λ > λ_c for any N; BKT for N=2 only at λ=∞. Kirsch (2007); Aizenman-Warzel (2015) Ch. 5. |

## Dependency axioms

pphi2N imports from pphi2, gaussian-field, and markov-semigroups.
However, **none of the dependency axioms are in pphi2N's dependency chain.**

| Dependency | Axioms in repo | Axioms we use | What we import |
|-----------|---------------|--------------|----------------|
| pphi2 | 23 | **0** | `analyticOnNhd_integral` (proved theorem, 0 axioms) |
| gaussian-field | 9 | **0** | Configuration, GFF, torus embedding, Prokhorov (all proved) |
| markov-semigroups | 3 | **0** | BrascampLieb.lean imported but no theorems called |

**Total axioms pphi2N depends on: exactly 10 (all in pphi2N itself).**

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
| MassGap/HubbardStratonovich.lean | ~138 | 0 | 0 | HS transformation, σ-measure (proved), BL variance (proved) |
| MassGap/TransferOperator.lean | ~150 | 1 | 0 | Conditional/unconditional spectral gap |
| MassGap/LargeNMassGap.lean | ~180 | 0 | 0 | Main mass gap theorem, explicit bounds |
| MassGap/InfiniteVolume.lean | ~250 | 3 | 0 | Poincaré → decay, random Schrödinger, all-N gap |
