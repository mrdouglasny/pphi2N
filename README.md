# pphi2N: O(N) P(φ)₂ and the NLSM Mass Gap

## What this project is

The O(N)-symmetric P(φ)₂ and nonlinear sigma model in two dimensions,
studied rigorously as a function of N. Building on the pphi2
construction (Glimm-Jaffe in Lean 4), we develop the σ-field
(invariant field) approach to prove mass gaps at large N.

## The three results

### Result 1: 1/N expansion with controlled remainders

The O(N)-invariant Schwinger functions have an asymptotic 1/N
expansion with rigorous error bounds (Brascamp-Lieb on the convex
σ-integral). Details: `docs/polynomial-in-N.md`

### Result 2: The invariant-field measure and FRG

The σ-field σ(x,y) = φ(x)·φ(y) carries a rigorous measure ν_N =
π_*μ_N. Its log-density is the effective potential V(σ), which
satisfies the Wetterich FRG equation. At non-integer n: ν_n is a
signed measure (nonperturbative but indefinite). At integer N: ν_N is
a genuine probability measure. Details: `docs/frg-invariant-field.md`

### Result 3: NLSM mass gap via LSM → NLSM limit

The O(N) NLSM is the λ → ∞ limit of the O(N) linear sigma model
(LSM) with potential λ(|φ|² - Nv²)². The LSM σ-integral IS convex
(Brascamp-Lieb applies). The mass gap transfers to the NLSM in the
limit. Combined with Balaban's block-spin RG for the continuum limit:

**Target theorem.** *The O(N) NLSM on T² has a mass gap for
N ≥ N₀, via:*
1. *LSM mass gap at finite λ (convex σ-measure, Brascamp-Lieb)*
2. *LSM → NLSM as λ → ∞ (finite-dim weak convergence)*
3. *Continuum limit a → 0 (Balaban block-spin, asymptotic freedom)*
4. *Infinite volume L → ∞ (gap equation monotonicity)*

Details: `docs/lsm-to-nlsm.md`

## The key idea: σ gives mass to all modes

The σ-field σ(x) = |φ(x)|²/N acts as a common mass for ALL N
components of φ (radial and Goldstone alike). The conditional
φ-measure (Gaussian with covariance (-Δ + σ)⁻¹) has mass √σ.

If the σ-measure concentrates near σ* > 0 (from Brascamp-Lieb:
Var(σ) ≤ C/(Nλ) for the LSM), then σ(x) ≥ σ*/2 everywhere with
high probability, and ALL modes have mass ≥ √(σ*/2). Goldstone
modes don't cause trouble because σ is a scalar potential.

## Documents

| Doc | Content |
|-----|---------|
| `docs/polynomial-in-N.md` | 1/N expansion: corrected statement, proof outline, degree bounds |
| `docs/frg-invariant-field.md` | FRG on σ-field: Wetterich equation, LPA, lattice derivation, mass gap bounds, NLSM caveats |
| `docs/lsm-to-nlsm.md` | LSM → NLSM limit: convexity, Brascamp-Lieb, λ→∞, Balaban continuum limit, three-step program |

## Dependencies

- [pphi2](https://github.com/mrdouglasny/pphi2) — P(φ)₂ construction
- [gaussian-field](https://github.com/mrdouglasny/gaussian-field) — GFF
- [graphops-qft](https://github.com/mrdouglasny/graphops-qft) — graphops, TRG

## Related

- `~/Desktop/work/categorical-qft/` — Deligne categories, saturated
  theories, space of QFTs (conceptual framework)
- `~/Documents/Github/rg/` — numerical TRG, RP/CP preservation, EKR

## References

- Glimm and Jaffe, *Quantum Physics*, Springer, 1987
- Simon, *The P(φ)₂ Euclidean QFT*, Princeton, 1974
- Brascamp and Lieb, JFA 22 (1976) — the inequality
- Kupiainen, CMP 73 (1980) — NLSM at N = ∞
- Balaban, CMP 96-122 (1983-1998) — block-spin RG for NLSM
- Moshe and Zinn-Justin, Phys. Rep. 385 (2003) — large N review
- Wetterich, Phys. Lett. B 301 (1993) — FRG equation
- Binder and Rychkov, JHEP 04 (2020) 117, arXiv:1911.07895 — Deligne categories
