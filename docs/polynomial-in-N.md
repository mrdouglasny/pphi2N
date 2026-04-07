# The Schwinger Functions Are Polynomials in N

## Statement

**Theorem.** Let P(t) = Σ_{k=2}^d a_k t^k be a polynomial bounded
below (a_d > 0, d even). For each integer N ≥ 1, let μ_N be the
O(N) P(φ)₂ measure on T²_L with interaction :P(φ·φ): and mass m > 0.

For any O(N)-invariant test functions f₁, ..., f_p ∈ S(T²), the
Schwinger function:

$$S_p(f_1, \ldots, f_p; N) := \int \prod_{j=1}^p (\phi \cdot f_j) \, d\mu_N$$

is a polynomial in N of degree ≤ p.

More generally, for any O(N)-invariant observable F:

$$\langle F \rangle_{\mu_N} = \sum_{q=0}^{\deg(F)} c_q(F) \cdot N^q$$

where the coefficients c_q depend on the test functions, coupling
constants, mass, and lattice parameters, but NOT on N.

## Proof outline

### Step 0: The lattice partition function is polynomial in N

On a finite lattice Λ with |Λ| sites, the partition function:

$$Z_\Lambda(N) = \int_{\mathbb{R}^{N|\Lambda|}} \prod_x d\phi(x) \, e^{-S[\phi]}$$

where S = (free action) + (interaction). Every closed O(N) index loop
contributes a factor of N = δ^i_i. The number of loops is determined
by the Feynman diagram / Brauer algebra combinatorics. Hence Z_Λ(N)
is a polynomial in N.

**Proof:** Expand e^{-V} in powers of the interaction. Each term is
a product of Wick contractions (from the GFF measure) and O(N)
contractions (from the interaction vertices). The Wick contractions
are N-independent (they come from the single-component propagator
G(x,y)). The O(N) contractions are Brauer algebra elements, each
producing a polynomial in N.

The total contribution of a Feynman diagram with k vertices and
ℓ O(N) loops is: (coupling)^k × (Wick factor) × N^ℓ. Summing
over all diagrams: Z_Λ(N) = Σ_diagrams c_diagram × N^{ℓ_diagram}.

### Step 1: Wick ordering is polynomial in N

The Wick-ordered interaction :P(φ·φ):_c is an explicit polynomial
in φ·φ and c = G(x,x) (the Wick constant, independent of N), with
coefficients that are polynomials in N.

For example:
- :(φ·φ)²:_c = (φ·φ)² - 2(N+2)c(φ·φ) + N(N+2)c²
- :(φ·φ)³:_c = (φ·φ)³ - 3(N+4)c(φ·φ)² + 3(N+2)(N+4)c²(φ·φ)
               - N(N+2)(N+4)c³

The general formula: the Wick ordering of (φ·φ)^k involves the
polynomial (N)_k = N(N+2)(N+4)···(N+2k-2) (rising factorial with
step 2). These are polynomials in N of degree k.

**Derivation:** The Wick ordering subtracts the self-contractions
of the O(N) field. The number of self-contractions of k copies of
φ·φ = Σ_i (φ^i)² involves the O(N) trace, which gives the factors
of N+2k from the dimension of the symmetric tensor space.

### Step 2: Nelson estimate is polynomial in N

The key hypercontractivity bound:

$$\|e^{-V}\|_{L^p(\mu_{GFF})} \leq e^{C(N) \cdot |\Lambda|}$$

where V = λ ∫ :(φ·φ)²: dμ. The N-dependence of C(N):

By Cauchy-Schwarz on the O(N) indices:
$$(\phi \cdot \phi)^2 = \left(\sum_i (\phi^i)^2\right)^2 \leq N \sum_i (\phi^i)^4$$

So the N-component quartic interaction is bounded by N times the
single-component quartic. Hence C(N) ≤ N · C(1) + O(1).

More precisely: the Nelson estimate for P(φ·φ) involves the single-
component Nelson estimate plus combinatorial factors from the O(N)
contractions, all polynomial in N.

### Step 3: Tightness is uniform in N

The second moment bound ⟨f, G_a f⟩ ≤ C(f) (from the lattice
propagator convergence) is INDEPENDENT of N — it's a property of
the single-component propagator G_a(x,y), which doesn't depend on N.

The Mitoma criterion gives tightness uniformly in N.

### Step 4: Continuum limit preserves polynomiality

At each lattice spacing a: the O(N)-invariant correlation functions
C_a(f₁,...,f_p; N) are polynomials in N (Step 0).

As a → 0: C_a(f₁,...,f_p; N) → C(f₁,...,f_p; N) for each integer N
(pphi2's continuum limit theorem).

The convergence is UNIFORM in N (Steps 2-3). A uniform limit of
polynomials in N (of bounded degree) is a polynomial in N. Hence
C(f₁,...,f_p; N) is a polynomial in N.

### Step 5: OS axioms hold at each integer N

From pphi2: the continuum measure μ_N satisfies OS0-OS4 for each
integer N ≥ 1. The O(N)-invariant Schwinger functions inherit all
OS properties.

## The degree bound

The O(N)-invariant Schwinger function S_p(f₁,...,f_p; N) has degree
≤ p/2 in N (each pair of test functions contributes at most one O(N)
loop). More precisely: the degree equals the number of independent
O(N) loops in the leading Feynman diagram.

For the 2-point function: degree 1 (one loop → one factor of N).
$$\langle (\phi \cdot f_1)(\phi \cdot f_2) \rangle = N \cdot \langle f_1, G f_2 \rangle$$

For the 4-point function: degree ≤ 2 (at most two loops).
$$\langle (\phi \cdot f_1) \cdots (\phi \cdot f_4) \rangle = N^2 (\cdots) + N (\cdots)$$

## Consequences

### 1. The nonperturbative O(n) P(φ)₂ theory

The polynomial interpolation defines ω_n for all n ∈ ℂ:
$$\omega_n(F) := \sum_{q=0}^{\deg(F)} c_q(F) \cdot n^q$$

This is a signed measure (continuous linear functional on observables).
It is nonperturbative (defined from the actual measures μ_N, not from
perturbation theory).

### 2. The RG flow acts on polynomials in n

Since the Schwinger functions are polynomials in n, the RG flow (which
maps Schwinger functions to Schwinger functions) acts on the finite-
dimensional space of polynomials at each degree. This is the
"saturated theory space" at parameter n.

### 3. Connection to the conformal bootstrap at general N

The bootstrap constraints (crossing symmetry, OPE convergence) applied
to the O(N) P(φ)₂ CFT are algebraic in N (they involve OPE
coefficients that are polynomials in N). The bootstrap at non-integer
n is the polynomial interpolation of the integer-N bootstrap.
