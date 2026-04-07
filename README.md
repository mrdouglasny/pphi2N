# O(N) P(φ)₂: Large N, Non-Integer N, and Categorical QFT

## What this project is

The O(N)-symmetric P(φ)₂ Euclidean quantum field theory in two
dimensions, studied as a function of N. Building on the rigorous
pphi2 construction (Glimm-Jaffe/pphi2 in Lean 4), we:

1. Prove the Schwinger functions are polynomials in N
2. Define the nonperturbative theory at non-integer n via
   polynomial interpolation (a signed measure, not a probability
   measure)
3. Study the mass gap m(n) as a function of n
4. Connect to Deligne categories and the Binder-Rychkov framework
5. Explore the space of O(n)-saturated theories and RG flow

## The main theorem (near-term goal)

**Theorem.** *The O(N)-invariant Schwinger functions of the P(φ)₂
theory with interaction P(φ·φ) on T² are polynomials in N. The
polynomial interpolation to n ∈ ℂ defines a nonperturbative
signed measure ω_n on the observable algebra. At each integer
N ≥ 1, ω_N agrees with the Glimm-Jaffe probability measure μ_N.*

Proof: trace the N-dependence through each step of the pphi2
construction (lattice GFF, Wick ordering, Nelson estimate,
tightness, continuum limit, OS axioms).

## The research program (longer-term)

### The mass gap m(n)

At integer N ≥ 1: the mass gap is positive (proved in pphi2).
As a function of n:
- Is m(n) a polynomial in n? (Probably not — it involves a
  nonlinear eigenvalue problem.)
- Is m(n) analytic in n? (Probably yes for P(φ)₂; less clear
  for the NLSM where BKT physics at n=2 might create a branch
  point.)
- What is the behavior as n → 0, n → ∞?

### The signed measure ω_n

At non-integer n: ω_n is a signed measure (indefinite linear
functional on observables). Properties:
- Polynomial in n (by construction)
- Positive at integer N (= probability measure μ_N)
- Indefinite at non-integer n (non-unitarity, Binder-Rychkov)
- Determines all O(n)-invariant observables nonperturbatively

The signed measure is the "Level 1.5" framework between the
algebraic Brauer computation (Level 1) and the probability
measure (Level 2).

### Deligne categories and saturated theories

A saturated theory w.r.t. O(n): every d.o.f. is an object in
Rep̃(O(n)), every interaction is a morphism, Z is polynomial in n.
The O(N) P(φ)₂ theory IS saturated (the field φ^i is the
fundamental object [1], the interaction (φ·φ)^k is a Brauer
morphism).

Connection to Binder-Rychkov (arXiv:1911.07895): their framework
for lattice models with categorical O(n) symmetry applies to the
lattice regularization of P(φ)₂. Our theorem extends this to the
continuum limit.

### The space of theories

For M O(N) vector fields with general O(N)-invariant interactions:
the theory space at quartic order has dimension growing with M.
The RG flow acts on this space, preserving the O(n) categorical
symmetry (Binder-Rychkov). Fixed points = O(n) CFTs.

### O(N) NLSM

The nonlinear sigma model with target S^{N-1}. Asymptotically
free for N ≥ 3 in 2D. Mass gap generated nonperturbatively.
The n-dependence of the mass gap is a deep question — possible
non-analyticity at n = 2 (BKT).

## Dependencies

- [pphi2](https://github.com/mrdouglasny/pphi2) — the P(φ)₂
  construction (Lean 4)
- [gaussian-field](https://github.com/mrdouglasny/gaussian-field) —
  GFF infrastructure
- [graphops-qft](https://github.com/mrdouglasny/graphops-qft) —
  graphop framework, TRG, cobordisms

## Related

- `~/Desktop/work/categorical-qft/` — research notes on saturated
  theories, Deligne categories, the space of QFTs
- `~/Documents/Github/rg/` — numerical TRG, RP/CP preservation,
  EKR proofs

## References

- Glimm and Jaffe, *Quantum Physics*, Springer, 1987
- Binder and Rychkov, "Deligne Categories in Lattice Models and QFT,"
  JHEP 04 (2020) 117, arXiv:1911.07895
- Ebel, Kennedy, Rychkov, arXiv:2506.03247 (rigorous TRG)
- Simon, *The P(φ)₂ Euclidean QFT*, Princeton, 1974
