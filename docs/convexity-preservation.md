# Convexity Preservation: The Bridge Between Balaban and Brascamp-Lieb

## The Problem

We have two tools that work at different scales:

- **Balaban's block-spin RG** (UV, scales a to L): takes the continuum
  limit a → 0 in a box of size L, controlled by asymptotic freedom.
  Output: an effective action S_eff^{(L)}[σ] at scale L.

- **Our Brascamp-Lieb argument** (IR, scales L to ∞): proves the mass
  gap from σ-concentration, using convexity of S_eff.

The bridge: does Balaban's block-spin **preserve the convexity** of
S_eff? If yes, we can apply Brascamp-Lieb to Balaban's output and
get the mass gap in the continuum.

## The Answer: Yes (Prékopa-Leindler)

**Prékopa-Leindler theorem** (1971/1973): If μ is a log-concave
measure on ℝ^{m+n} (i.e., dμ = e^{-V} dx with V convex), then the
marginal on ℝ^m (obtained by integrating out the ℝ^n variables) is
also log-concave.

Equivalently: if V(x, y) is convex in (x, y) ∈ ℝ^{m+n}, then

$$W(x) = -\log \int e^{-V(x,y)}\, dy$$

is convex in x ∈ ℝ^m.

**Application to block-spin:** Each Balaban block-spin step integrates
out the short-wavelength fluctuations within a block. This is exactly
a marginalization — projecting from a finer space to a coarser one.
If the action before the step is convex (in the σ-field), the action
after the step is also convex.

## The Argument in Detail

### The starting point: LSM at lattice spacing a

The LSM effective action for the σ-field on a lattice with spacing a,
|Λ| = (L/a)² sites:

$$S_{\text{eff}}^{(a)}[\sigma] = \frac{N}{2}\,\text{Tr}\log(-\Delta_a + \sigma) + N\sum_x \lambda(\sigma(x) - v^2)^2$$

This is convex in σ for λ large enough (the λ-term dominates the
concave Tr log Hessian). Specifically:

$$S''_{\text{eff}} = -\frac{N}{2}G_a[\sigma]^2 + 2N\lambda \cdot I$$

The first term is negative (concave from Tr log) with operator norm
≤ (N/2) · ‖G_a‖²_∞. The second term is 2Nλ · I (convex). So:

$$S''_{\text{eff}} \geq (2N\lambda - \frac{N}{2}\|G_a\|^2_\infty) \cdot I$$

Convexity holds when $\lambda > \|G_a\|^2_\infty / 4$.

### Step 1: Balaban's first block-spin (a → 2a)

Average the σ-field over 2×2 blocks. The block-averaged σ lives on a
coarser lattice with spacing 2a. The fine-grained fluctuations
(within each block) are integrated out.

Formally: write σ = σ_coarse + δσ where σ_coarse is block-constant
and δσ has zero block-average. Then:

$$S_{\text{eff}}^{(2a)}[\sigma_{\text{coarse}}] = -\log \int D(\delta\sigma)\, e^{-S_{\text{eff}}^{(a)}[\sigma_{\text{coarse}} + \delta\sigma]}$$

By Prékopa-Leindler: if $S_{\text{eff}}^{(a)}$ is convex in the full
σ (both coarse and fine modes), then $S_{\text{eff}}^{(2a)}$ is
convex in σ_coarse.

**Key:** The convexity is in the FULL σ-field (all modes), not just
in the block-averaged part. The LSM action IS convex in the full σ
(for large enough λ), so the block-spin preserves it.

### Step 2: Iterate (2a → 4a → ... → L)

Each block-spin step doubles the spacing: ka → 2ka. At each step:

$$S_{\text{eff}}^{(2^{j+1}a)} = -\log \int D(\delta\sigma)\, e^{-S_{\text{eff}}^{(2^j a)}}$$

By induction on j: if $S_{\text{eff}}^{(2^j a)}$ is convex, then
$S_{\text{eff}}^{(2^{j+1} a)}$ is convex (Prékopa-Leindler).

After k = log₂(L/a) steps: $S_{\text{eff}}^{(L)}$ is the effective
action on a SINGLE block of size L. It is convex.

### Step 3: Brascamp-Lieb on the final effective action

The σ-field on the single block has finitely many modes (the
zero mode + a few low-momentum modes if L is not too large). Apply
Brascamp-Lieb to $S_{\text{eff}}^{(L)}$:

$$\text{Var}_{\nu_N}(\sigma) \leq \frac{1}{N} \cdot \frac{1}{\inf S''^{(L)}_{\text{eff}}}$$

The gap equation determines σ* > 0 (the minimum of $S_{\text{eff}}^{(L)}$).
The σ-concentration gives σ(x) ≥ σ*/2 > 0 → mass gap.

## The Continuum Limit

Balaban's block-spin also takes a → 0 (by adding more initial
block-spin steps at finer lattice spacings). The key:

- At each step, the effective coupling g²(2^j a) decreases
  (asymptotic freedom)
- The convexity constant $2N\lambda - (N/2)\|G\|^2$ stays positive
  (the λ-term from the LSM potential persists through the RG)
- Actually: as the lattice is coarsened, the "effective λ" at scale
  2^j a may change. Need to track how the convexity constant evolves.

**The crucial question:** Does the convexity constant
$\inf S''_{\text{eff}}$ stay bounded below through ALL Balaban steps?

Prékopa-Leindler says: convexity is PRESERVED (not strengthened).
So the infimum of S'' can only decrease (or stay the same). We need
it to stay positive.

For the LSM: the initial $\inf S'' \geq 2N\lambda - (N/2)\|G_a\|^2$.
After k steps: $\inf S''^{(2^k a)} \geq$ ??? This depends on how
the Tr log Hessian evolves under block-spin.

**Balaban's contribution here:** His estimates show the effective
action stays bounded (UV stability). The convexity constant should
be controlled by his bounds. Specifically: the operator norm of the
coarse-grained propagator $\|G^{(L)}\|$ is bounded by Balaban's
estimates, which gives a lower bound on $\inf S''^{(L)}$.

## The Full Chain

$$\boxed{
\text{LSM (convex)} \xrightarrow{\text{Prékopa-Leindler}} 
\text{Block-spin (convex at each step)} \xrightarrow{\text{Balaban bounds}}
\text{Effective action at scale } L \text{ (convex)} \xrightarrow{\text{Brascamp-Lieb}}
\text{Mass gap}
}$$

1. Start: LSM at spacing a with λ large → $S_{\text{eff}}^{(a)}$ convex
2. Block-spin a → 2a → ... → L: convexity preserved (Prékopa-Leindler)
3. Balaban bounds: the convexity constant stays positive through the RG
4. Brascamp-Lieb at scale L: σ concentrates → mass gap ≥ √(σ*/2)
5. Take L → ∞: gap equation gives σ*(L) → σ*_∞ > 0 → mass gap persists

### Then take λ → ∞ (LSM → NLSM)

At each stage of the block-spin: we have the LSM at some effective
(λ, g²) at that scale. Taking λ → ∞ at the end gives the NLSM.

But we can also take λ → ∞ FIRST (on the lattice, before
block-spinning) to get the lattice NLSM, then apply Balaban's
block-spin to the lattice NLSM directly.

The question: does Prékopa-Leindler apply to the NLSM σ-integral?

No — the NLSM σ-integral is CONCAVE (no λ-term). Prékopa-Leindler
doesn't help.

**The fix:** Keep λ finite but large throughout the block-spin.
Take λ → ∞ only AFTER the continuum limit. The convexity is
maintained at every intermediate step.

The order of limits:
$$\lim_{\lambda \to \infty}\, \lim_{a \to 0}\, \lim_{L \to \infty}\, [\text{LSM at } (\lambda, a, L)]$$

Each limit preserves the mass gap:
- $L \to \infty$: gap equation monotonicity
- $a \to 0$: Balaban + Prékopa-Leindler convexity preservation
- $\lambda \to \infty$: weak convergence (mass gap lower semicontinuous)

## What Needs to Be Proved

| Step | Tool | Status |
|---|---|---|
| LSM $S_{\text{eff}}$ is convex | Direct computation | Straightforward for $\lambda > \lambda_0$ |
| Block-spin preserves convexity | Prékopa-Leindler theorem | Standard (textbook) |
| Convexity constant stays positive through RG | Balaban's UV stability bounds | Needs to extract from Balaban's estimates |
| Brascamp-Lieb → mass gap at scale L | Brascamp-Lieb + Sobolev embedding | Standard |
| Gap equation σ*(L) bounded below as L → ∞ | Analysis of the gap equation | Standard (Kupiainen 1980 at N=∞) |
| λ → ∞ preserves mass gap | Weak convergence + lower semicontinuity | Standard (finite-dim) |

The only step that requires new work: extracting the convexity
constant from Balaban's estimates. Everything else uses existing
tools (Prékopa-Leindler, Brascamp-Lieb, Kupiainen's gap equation,
weak convergence).

## References

- Prékopa, "Logarithmic concave measures," Acta Sci. Math. 34 (1973)
- Brascamp and Lieb, JFA 22 (1976) — the Brascamp-Lieb inequality
- Balaban, CMP 96-122 (1983-1998) — block-spin RG for NLSM
  (especially: "Ultraviolet stability in field theory. The φ⁴₃
  model" and the NLSM papers)
- Kupiainen, CMP 73 (1980) — gap equation at N = ∞
