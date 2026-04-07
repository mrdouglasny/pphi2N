# Master Field and Large-N Limit: Formalization Plan

## Overview

For the O(N) P(φ)₂ theory with N real scalar fields φⁱ(x), the
**master field** is the O(N)-invariant bilinear:

$$G(x,y) = \frac{1}{N} \sum_{i=1}^N \phi^i(x) \phi^i(y)$$

The interacting measure μ_N on N-component fields pushes forward to a
measure ν_N on the space of master fields. As N → ∞, ν_N concentrates
on a deterministic limit G_∞ (the solution of the gap equation), with
1/N corrections described by Gaussian fluctuations.

## Targets

### Theorem 1: Pushforward existence
The map φ ↦ G(f,g) = (1/N) Σᵢ φⁱ(f)φⁱ(g) is measurable, so the
interacting measure pushes forward to a measure on the master field space.

### Theorem 2: Schwinger functions polynomial in N
The master field Schwinger functions (expectations of products of G(fₐ,gₐ))
are polynomials in N. This follows from the Wick ordering being polynomial
in N (proved in ONWick.lean) and the interaction being O(N)-invariant.

### Theorem 3: Factorization at large N
Connected k-point functions of G scale as N^{1-k}:
- ⟨G(f,g)⟩ = O(1)
- ⟨G(f₁,g₁) G(f₂,g₂)⟩_c = O(1/N)
- ⟨G(f₁,g₁) G(f₂,g₂) G(f₃,g₃)⟩_c = O(1/N²)

### Theorem 4: Classical limit
The pushforward measure ν_N converges weakly to a delta measure:
ν_N → δ_{G_∞} as N → ∞, where G_∞ solves the gap equation.

### Theorem 5: Central limit theorem
√N · (G - G_∞) converges in distribution to a Gaussian field with
covariance determined by S_eff''(σ_*).

## File structure

```
Pphi2N/
  Model/
    Interaction.lean          -- ONInteraction (done)
    ONModel.lean              -- ONModel (done)
  LatticeField/
    NComponentField.lean      -- N-component field (done)
    ONGaussian.lean           -- O(N) GFF, Wick constant (done)
  WickOrdering/
    ONWick.lean               -- Wick monomials, recursion (done)
  MasterField/
    MasterField.lean          -- master field definition, pushforward
    MasterFieldMoments.lean   -- moments of G, polynomial in N
    Factorization.lean        -- connected correlators scale as N^{1-k}
  LargeN/
    EffectiveAction.lean      -- S_eff[σ] from Hubbard-Stratonovich
    GapEquation.lean          -- Schwinger-Dyson / gap equation for G_∞
    ClassicalLimit.lean       -- ν_N → δ_{G_∞}
    FluctuationCLT.lean       -- √N(G-G_∞) → Gaussian
  InteractingMeasure/
    ONLatticeAction.lean      -- lattice action for N-component field
    ONNelsonEstimate.lean     -- Nelson bound (N-dependent constants)
    ONInteractingMeasure.lean -- interacting measure on T² or Λ
  ContinuumLimit/
    ONTightness.lean          -- tightness uniform in N
    ONContinuumLimit.lean     -- continuum limit exists for each N
    NUniformBounds.lean       -- bounds uniform in both a and N
```

## Phase 1: Master field on the lattice (Theorems 1-2)

### 1.1 Master field definition

On a finite lattice Λ with N-component field φ : Λ → ℝ^N:

```lean
-- Smeared master field: for test functions f, g : Λ → ℝ
def masterFieldSmeared (N : ℕ) (φ : NComponentField N Λ) (f g : Λ → ℝ) : ℝ :=
  (1 / N : ℝ) * ∑ i : Fin N, (∑ x, f x * φ x i) * (∑ y, g y * φ y i)

-- Pointwise master field
def masterFieldPointwise (N : ℕ) (φ : NComponentField N Λ) (x y : Λ) : ℝ :=
  (1 / N : ℝ) * ∑ i : Fin N, φ x i * φ y i
```

### 1.2 Pushforward measurability

The master field is a quadratic function of φ, hence measurable.
The pushforward measure ν_N = (masterField)_* μ_N is well-defined.

Key lemma: for any bounded measurable F on the master field space,
∫ F(G) dν_N = ∫ F(masterField(φ)) dμ_N.

### 1.3 Moments are polynomial in N

**Lattice level (finite-dimensional).** For the lattice GFF with
covariance ⟨φⁱ(x)φʲ(y)⟩ = δⁱʲ C(x,y):

⟨G(x₁,y₁) ··· G(x_p,y_p)⟩ = N^{-p} Σ_{i₁...i_p}
    ⟨φ^{i₁}(x₁)φ^{i₁}(y₁) ··· φ^{i_p}(x_p)φ^{i_p}(y_p)⟩

By Wick's theorem (Gaussian case), this is a sum over pairings.
Each pairing contributes a product of C(·,·) times an O(N) index
contraction, which is a polynomial in N (from the Brauer algebra).

For the interacting case: expand e^{-V} and use the same argument.
The Wick-ordered interaction is polynomial in N (from ONWick.lean),
so each term in the perturbation series is polynomial in N. The
convergence of the series (from the Nelson estimate) preserves
polynomiality since we're on a finite lattice.

### 1.4 Key Lean structures

```lean
-- The master field observable algebra
structure MasterFieldObs (Λ : Type*) [Fintype Λ] where
  -- An observable is a function of the master field G(·,·)
  obs : (Λ → Λ → ℝ) → ℝ

-- The pushforward: integrate observables against ν_N
def masterFieldExpectation (N : ℕ) (μ : Measure (NComponentField N Λ))
    (F : MasterFieldObs Λ) : ℝ :=
  ∫ φ, F.obs (masterFieldPointwise N φ) ∂μ
```

## Phase 2: Free theory moments (Theorem 3 for GFF)

### 2.1 Wick's theorem for the master field

For the GFF, ⟨G(x,y)⟩ = C(x,y) (the propagator, independent of N).

The connected 2-point function:
⟨G(x₁,y₁) G(x₂,y₂)⟩_c = (1/N)[C(x₁,x₂)C(y₁,y₂) + C(x₁,y₂)C(y₁,x₂)]

This is O(1/N) — the fluctuations of the master field are small.

For the k-point connected correlator: O(1/N^{k-1}).

### 2.2 Proof structure

The Wick contractions for ⟨Π_a G(x_a,y_a)⟩ produce:
- N^{-p} × (sum over Wick pairings) × (O(N) index sum)
- Each O(N) index sum = N^{number of loops}
- A connected p-point function has at most 1 loop, giving N^1
- So connected p-point = N^{-p} × N^1 × (propagator product) = O(N^{1-p})

This is the standard large-N counting for vector models.

## Phase 3: Interacting theory (Theorems 3-4)

### 3.1 Hubbard-Stratonovich transformation

Introduce auxiliary field σ(x) and use the identity:
exp(-λ(φ·φ)²) = ∫ dσ exp(-σ²/(4λ) + iσ φ·φ)

After integrating out the N Gaussian fields φⁱ (each sees the
potential σ(x) as an external field):

Z_N[σ] = det(-Δ + m² + iσ)^{-N/2}

The effective action is:
S_eff[σ] = (N/2) Tr log(-Δ + m² + iσ) + Σ_x σ(x)²/(4λ)

The factor of N in front makes the σ-integral a saddle-point integral
at large N.

### 3.2 Gap equation

The saddle point σ_* satisfies:
∂S_eff/∂σ(x) = 0
⟹ σ_*(x)/(2λ) = (N/2) (-Δ + m² + iσ_*)^{-1}(x,x)

In terms of G_∞ = (-Δ + m² + iσ_*)^{-1}:
σ_*(x) = λ N G_∞(x,x)

This is the self-consistent equation: the auxiliary field σ_* is
determined by the diagonal of the propagator G_∞, which depends on σ_*.

On the lattice (finite Λ), this is a finite-dimensional fixed-point
equation: σ ∈ ℝ^|Λ| → F(σ) ∈ ℝ^|Λ|, and σ_* = F(σ_*).

### 3.3 Classical limit

The saddle-point approximation becomes exact as N → ∞:

∫ dσ exp(-N · S_eff[σ]) → exp(-N · S_eff[σ_*]) × (Gaussian corrections)

The Gaussian corrections contribute O(1) to log Z (not O(N)), so:
- Free energy: F_N = N · S_eff[σ_*] + O(1)
- Master field: G_N → G_∞ = (-Δ + m² + iσ_*)^{-1}
- Convergence: ν_N → δ_{G_∞}

### 3.4 Lean formalization

```lean
-- The gap equation on a finite lattice
def gapEquation (Λ : Type*) [Fintype Λ]
    (laplacian : Matrix Λ Λ ℝ) (mass : ℝ) (P : ONInteraction)
    (σ : Λ → ℝ) : Prop :=
  ∀ x : Λ, σ x = P.eval' ((laplacian + mass^2 + diag σ)⁻¹ x x)
  -- where P.eval' is the derivative of P

-- Existence of solution (Brouwer fixed-point on finite lattice)
theorem gapEquation_exists : ∃ σ, gapEquation Λ laplacian mass P σ := by
  sorry -- Brouwer or Schauder fixed-point theorem
```

## Phase 4: 1/N fluctuations (Theorem 5)

### 4.1 Fluctuation field

Define η_N = √N · (G - G_∞) as a random bilinear form. The CLT gives:

η_N →_d η where η is Gaussian with covariance:
Cov(η(x₁,y₁), η(x₂,y₂)) = G_∞(x₁,x₂)G_∞(y₁,y₂) + G_∞(x₁,y₂)G_∞(y₁,x₂)
                            + (vertex corrections from interaction)

### 4.2 Higher-order 1/N corrections

The systematic expansion:
⟨F[G]⟩_N = F[G_∞] + (1/N) · F₁ + (1/N²) · F₂ + ...

where F_k involves k-loop diagrams in the σ-field theory. For vector
models (not matrix models), this is an expansion in 1/N (not 1/N²).

### 4.3 Convergence

For P(φ)₂ in 2D with quartic interaction:
- The 1/N expansion is expected to be CONVERGENT (not just asymptotic)
- This follows from the polynomial-in-N property + bounds on coefficients
- The convergence radius in 1/N may extend to include N=1 (recovering
  the single-component P(φ)₂ theory)

## Phase 5: Continuum limit

### 5.1 N-uniform bounds

The continuum limit (lattice spacing a → 0) should commute with the
large-N limit. This requires bounds uniform in BOTH a and N:

- Nelson estimate: ‖e^{-V}‖_{L^p} ≤ exp(C(N)·|Λ|) with C(N) = O(N)
- Tightness: Mitoma-Chebyshev with N-dependent seminorms
- Moment bounds: ∫(ωf)² ≤ C·N·q(f)² (the N factor from c_N = Nc₁)

### 5.2 Double limit

Three limits to consider:
1. a → 0 with N fixed (continuum limit at finite N) — done in pphi2
2. N → ∞ with a fixed (large-N limit on lattice) — new
3. a → 0, N → ∞ simultaneously — the double limit

The polynomial-in-N property suggests that limits 1 and 2 commute
(the continuum Schwinger functions are still polynomial in N).

## Dependencies

- **pphi2**: The N=1 case, lattice measure construction, Nelson estimate,
  tightness, OS axioms. We reuse the proof architecture.
- **gaussian-field**: GFF infrastructure, DM spaces, nuclear tensor products
- **Mathlib**: Measure theory, finite-dimensional analysis, Brouwer
  fixed-point theorem

## Estimated effort

| Phase | Files | Lines | Difficulty |
|-------|-------|-------|-----------|
| 1: Master field + moments | 3 | ~400 | Medium |
| 2: Free theory counting | 2 | ~300 | Medium |
| 3: Interacting (HS, gap eq) | 3 | ~500 | Hard |
| 4: CLT for fluctuations | 2 | ~400 | Hard |
| 5: Continuum limit | 3 | ~500 | Hard (reuses pphi2) |

Total: ~13 files, ~2100 lines.

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I–II
- Glimm-Jaffe, *Quantum Physics*, Ch. 6, 19
- Moshe-Zinn-Justin, "Quantum field theory in the large N limit: a review"
  Physics Reports 385 (2003) 69-228
- Binder-Rychkov, "Deligne Categories in Lattice Models and QFT,"
  JHEP 04 (2020) 117
- Kupiainen, "Renormalization group and stochastic PDEs", Ann. Henri Poincaré 2016
