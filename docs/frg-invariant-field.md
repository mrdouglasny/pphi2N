# The Functional RG on the Invariant Field Space

## 1. The Wetterich Equation

The functional renormalization group (FRG) defines the RG as a flow
on the space of effective actions. The central object is the
**effective average action** $\Gamma_k[\sigma]$, a scale-dependent
functional that interpolates between:

- $k = \Lambda$ (UV cutoff): $\Gamma_\Lambda = S_{\text{bare}}$
- $k = 0$ (no cutoff): $\Gamma_0 = \Gamma$ (full quantum effective action)

The **Wetterich equation** (1993):

$$\partial_t \Gamma_k[\sigma] = \frac{1}{2} \mathrm{Tr}\left[\frac{\partial_t R_k}{\Gamma_k^{(2)}[\sigma] + R_k}\right]$$

where $t = \log(k/\Lambda)$, $\Gamma_k^{(2)}$ is the second functional
derivative (= inverse propagator at scale $k$), and $R_k(p^2)$ is a
regulator that suppresses modes with $p < k$.

This equation is **exact** — a single equation encoding the full
nonperturbative RG flow. The RHS has a one-loop structure (a single
trace), but it involves the full $\Gamma_k$ (not the bare action),
so it resums all loops.

### References

- Wetterich, "Exact evolution equation for the effective potential,"
  Phys. Lett. B 301 (1993) 90-94
- Berges, Tetradis, Wetterich, "Non-perturbative renormalization flow
  in quantum field theory and statistical physics," Phys. Rep. 363
  (2002) 223-386
- Morris, "The exact renormalization group and approximate solutions,"
  Int. J. Mod. Phys. A 9 (1994) 2411

## 2. The Local Potential Approximation (LPA)

The exact flow is a functional PDE (infinite-dimensional). The
simplest truncation: keep the full potential $V_k(\sigma)$ but
drop field-dependent kinetic terms.

**Ansatz:**
$$\Gamma_k[\sigma] = \int d^dx\, \left[\frac{1}{2}(\partial\sigma)^2 + V_k(\sigma)\right]$$

The Wetterich equation reduces to a PDE for $V_k$:

$$\partial_t V_k(\sigma) = \frac{1}{2}\int \frac{dp\; \partial_t R_k(p^2)}{p^2 + R_k(p^2) + V''_k(\sigma)}$$

This is a **1+1 dimensional PDE**: one variable $t$ (RG "time"),
one variable $\sigma$ (the field). The "initial condition" at
$t = 0$ is $V_\Lambda(\sigma) = V_{\text{bare}}(\sigma)$.

With a sharp cutoff regulator $R_k(p^2) = (k^2 - p^2)\theta(k^2 - p^2)$
in $d$ dimensions:

$$\partial_t V_k(\sigma) = \frac{k^d}{2}\, \frac{\Omega_d}{(2\pi)^d}\, \frac{1}{k^2 + V''_k(\sigma)}$$

where $\Omega_d = 2\pi^{d/2}/\Gamma(d/2)$ is the solid angle.

## 3. The O(N) Model

For the O(N) model, use the radial variable $\rho = \phi \cdot \phi / (2N)$
(the O(N)-invariant field). The potential $V_k(\rho)$ and the flow
equation splits into Goldstone and radial contributions:

$$\partial_t V_k(\rho) = \frac{N-1}{2}\, I\!\left[V'_k(\rho)\right] + \frac{1}{2}\, I\!\left[V'_k(\rho) + 2\rho\, V''_k(\rho)\right]$$

where:

- First term: **(N-1) Goldstone modes** with mass$^2$ = $V'(\rho)$
- Second term: **1 radial mode** with mass$^2$ = $V'(\rho) + 2\rho V''(\rho)$
- $I[m^2] = \int dp\, \partial_t R_k(p^2) / (p^2 + R_k(p^2) + m^2)$
  is the "threshold function" (regulated one-loop integral)

**The N-dependence is explicit:** N appears as a coefficient of the
Goldstone contribution. The flow is polynomial in N (degree 0 and 1
in N at each step of the PDE evolution).

## 4. Leading Order in 1/N: Exact Solution

At $N \to \infty$, the Goldstone modes dominate (N-1 vs 1):

$$\partial_t V_k(\rho) \approx \frac{N}{2}\, I\!\left[V'_k(\rho)\right]$$

This is a **first-order PDE in $V'$** and can be solved by the method
of characteristics. Define $u = V'_k(\rho)$ (the "mass squared"):

$$\partial_t u = \frac{N}{2}\, I'[u] \cdot \partial_\rho u$$

The characteristic curves give the exact evolution of $V'$ along the flow.

### The gap equation

At the fixed point ($\partial_t V^* = 0$): $I[V'^*(\rho)] = 0$, which
gives $V'^*(\rho) = 0$ (the Gaussian fixed point) or $V'^*(\rho) = m^2_c$
(the critical mass, determined by the regulator).

For the Wilson-Fisher fixed point in $d = 4 - \epsilon$:

$$V^*(\rho) = \text{(explicit function determined by } I[m^2] = 0 \text{)}$$

### Exact critical exponents at leading 1/N

In $d$ dimensions at leading order in 1/N:

$$\eta = 0, \quad \nu = \frac{1}{d - 2}, \quad \gamma = \frac{2}{d-2}$$

These are exact (valid for all d, not just near d = 4).

### The effective potential at N = $\infty$ in d = 2

For our P($\phi$)$_2$ case ($d = 2$):

$$S_{\text{eff}}[\sigma] = \frac{N}{2}\left[\int \frac{d^2k}{(2\pi)^2} \log(k^2 + \sigma) + \int d^2x\, \frac{\sigma^2}{4\lambda}\right]$$

The gap equation:

$$\sigma^* = m_0^2 + \frac{\lambda N}{2\pi} \log\frac{\Lambda^2}{\sigma^*}$$

The theory is always massive (super-renormalizable, no phase transition
as a function of $\lambda$). The physical mass $m^2 = \sigma^*$ is
determined by this transcendental equation.

### References for the exact large N solution

- Moshe and Zinn-Justin, "Quantum field theory in the large N limit:
  a review," Phys. Rep. 385 (2003) 69-228 — the comprehensive reference
- D'Attanasio and Morris, "Large N and the renormalization group,"
  Phys. Lett. B 409 (1997) 363-370 — exact FRG at large N
- Tetradis and Wetterich, "Critical exponents from the effective
  average action," Nucl. Phys. B 422 (1994) 541-592

## 5. The Space of Theories

In the LPA, the space of theories at scale $k$ is the space of
functions $V : \mathbb{R}_{\geq 0} \to \mathbb{R}$ (potentials of
the radial variable $\rho$). This is an infinite-dimensional function
space.

**Truncation to polynomials:** Expand $V_k(\rho) = \sum_{n=0}^{n_{\max}} g_n(k)\, \rho^n$.
The flow equation becomes a system of ODEs for the couplings $g_n(k)$.

At order $n_{\max} = 2$: two couplings $(m^2, \lambda)$, the standard
$\phi^4$ flow.

At order $n_{\max} = 3$: three couplings $(m^2, \lambda, g_6)$, the
$\phi^4 + \phi^6$ flow with a tricritical point.

The fixed points (zeros of the beta functions) are the CFTs.

**The N-dependence of the flow:** At each truncation order, the beta
functions $\beta_{g_n}(g_0, \ldots, g_{n_{\max}}; N)$ are polynomial
in N. The fixed-point values $g_n^*(N)$ are algebraic functions of N
(solutions of polynomial equations). The critical exponents (eigenvalues
of the stability matrix at the fixed point) are also algebraic in N.

## 6. What's Rigorous and What's Formal

| Aspect | Status |
|---|---|
| The Wetterich equation | Formal (derived from path integral manipulations) |
| The LPA flow equation | Well-defined PDE (can study existence, uniqueness, regularity) |
| Existence of solutions to the LPA PDE | Standard PDE theory (parabolic, short-time existence) |
| Global existence and convergence to fixed points | Not proved in general |
| Fixed points of the LPA PDE | Found numerically; rigorous existence not proved |
| Connection to actual QFT measures | **Not proved** |
| The leading-order 1/N solution | Exact (the PDE reduces to characteristics) |

### The gap we can fill

The pphi2 construction gives **rigorous** measures $\mu_N$ for each
integer $N \geq 1$. The invariant-field measure $\nu_n$ (from Section 3e)
should satisfy the Wetterich equation — or more precisely, its
correlation functions should evolve according to the FRG flow.

Making this connection rigorous would:
1. Put the FRG on rigorous footing for P($\phi$)$_2$
2. Show that the formal FRG flow correctly describes the actual
   scale-dependence of the rigorous measures
3. Extend via polynomial interpolation to non-integer $n$
4. Give a nonperturbative definition of "the space of O(n) theories"
   as the space of invariant-field measures satisfying the FRG

## 7. Lattice FRG from the pphi2 Construction

### Three ways to put FRG on the lattice

**The pphi2 approach (implicit RG).** The pphi2 construction gives
rigorous measures $\mu_{N,a}$ at each lattice spacing $a$ and integer
$N$. As $a$ varies, $\mu_{N,a}$ changes — this change IS the RG flow,
expressed as a family of measures rather than a differential equation.

The Wetterich effective action is the Legendre transform of
$\log Z_a$. Making this dictionary precise connects the rigorous
measures to the formal FRG:

$$V_a(\sigma) = -\log \frac{d\nu_{N,a}}{d\nu_{N,a}^{\text{free}}}(\sigma)$$

where $\nu_{N,a} = \pi_* \mu_{N,a}$ is the invariant-field measure.

**The lattice Wetterich equation (direct).** Replace continuum momenta
with lattice momenta in the Brillouin zone $[-\pi/a, \pi/a]^d$:

$$\partial_t V_k(\sigma) = \frac{1}{2}\sum_{p \in \text{BZ}} \frac{\partial_t R_k(p^2_{\text{lat}})}{p^2_{\text{lat}} + R_k(p^2_{\text{lat}}) + V''_k(\sigma)}$$

where $p^2_{\text{lat}} = (4/a^2)\sum_j \sin^2(p_j a/2)$ is the
lattice dispersion relation. Same structure as the continuum equation,
with sums replacing integrals.

**TRG as discrete RG steps.** Each TRG step doubles the effective
lattice spacing ($a \to 2a$), coarse-grains via SVD, and produces a
new tensor = new effective action at scale $2a$. This is a
finite-step approximation to the Wetterich flow.

### The concrete program

At each lattice spacing $a$ and integer $N$, the pphi2 construction
gives:

1. A rigorous measure $\mu_{N,a}$ on field configurations
2. The invariant-field measure $\nu_{N,a} = \pi_* \mu_{N,a}$
3. The lattice effective potential $V_a(\sigma)$ = log-density of $\nu_{N,a}$

The sequence of coarse-grainings:

$$V_{a_0}(\sigma) \to V_{2a_0}(\sigma) \to V_{4a_0}(\sigma) \to \cdots$$

IS the lattice RG flow, computed rigorously from actual measures.

### Three questions

**Q1. Convergence to fixed point.** Does $V_{2^n a_0}(\sigma)$
converge to a fixed-point potential $V^*(\sigma)$ as $n \to \infty$
(at the critical coupling)? The fixed point IS the CFT potential.

For P($\phi$)$_2$ in $d = 2$: the theory is always massive (no phase
transition at fixed $\lambda > 0$), so $V^*(\sigma) = m^2 \sigma$
(quadratic = Gaussian fixed point). The flow converges to the massive
Gaussian, not to a nontrivial CFT.

For the O(N) NLSM in $d = 2$: the theory IS asymptotically free and
the fixed point is nontrivial (at $N \geq 3$). This is the more
interesting case.

**Q2. Continuum limit of the flow.** Does the discrete lattice flow
converge to the Wetterich PDE as $a \to 0$ with $k = 1/a$?

The lattice Wetterich equation (with lattice dispersion and Brillouin
zone sum) reduces to the continuum equation as $a \to 0$:
$\sin^2(pa/2) \to p^2 a^2/4$ and $\sum_p \to \int dp/(2\pi)^d$.
The convergence rate is $O(a^2)$ (from the lattice dispersion Taylor
expansion — the same $(1 - \cos)/a^2 \to k^2/2$ that pphi2 uses).

**Q3. Polynomial N-dependence.** Is $V_a(\sigma; N)$ a polynomial
in $N$ at each lattice spacing?

Yes — from the Brauer algebra structure: the lattice measure
$\mu_{N,a}$ has O(N)-invariant observables polynomial in N, hence
the invariant-field log-density is also polynomial in N. The LPA
flow equation preserves this: the $(N-1)$ and $1$ prefactors of the
Goldstone and radial modes are linear in $N$, and the flow PDE
preserves polynomial dependence.

### Rigorous error bounds at large but finite N

The comparison between finite $N$ and $N = \infty$ does NOT come from
the Nelson estimate (which gives existence at each $N$, not a
comparison). It comes from the **Laplace method** on the $\sigma$-integral:

$$Z(N) = \int D\sigma \; \exp\!\left(-\frac{N}{2}\, S_{\text{eff}}[\sigma]\right)$$

The factor $N/2$ in the exponent concentrates the integral at the
saddle $\sigma^*$ as $N \to \infty$.

**Key fact:** $S_{\text{eff}}[\sigma]$ is **convex** in $\sigma$ (for
$\sigma > 0$): $\text{Tr}\log(-\Delta + \sigma)$ is operator-concave,
so $-\text{Tr}\log$ is convex, and the $\sigma^2/(4\lambda)$ term is
convex. The measure $\exp(-N/2 \cdot S_{\text{eff}})$ is log-concave.

**Brascamp-Lieb inequality** (for log-concave measures):

$$\text{Var}_{\nu_N}(F) \leq \frac{1}{N} \cdot \frac{\langle |\nabla F|^2 \rangle}{\inf S''_{\text{eff}}}$$

This gives:

$$|\langle F \rangle_N - \langle F \rangle_\infty| \leq \frac{C(F)}{N}$$

for any smooth observable $F$ of the invariant field $\sigma$.

**The norms:**

| What's bounded | Norm | Bound |
|---|---|---|
| Single observable $\langle F \rangle$ | Pointwise | $|\langle F \rangle_N - \langle F \rangle_\infty| \leq C(F)/N$ |
| $k$-point Schwinger function | Sobolev dual $H^{-s}$ | $\|S_k(\cdot;N) - S_k(\cdot;\infty)\|_{H^{-s}} \leq C_k/N$ |
| Variance of $\sigma$-field | $L^2(\nu_N)$ | $\text{Var}(\sigma) \leq C/N$ |
| Free energy density | Per-volume scalar | $|f(N) - f(\infty)| \leq C/N$ |

The Laplace expansion gives the full asymptotic series:

$$\langle F \rangle_N = \langle F \rangle_\infty + \frac{a_1(F)}{N} + \frac{a_2(F)}{N^2} + \cdots$$

with remainder bounded: $|\langle F \rangle_N - \sum_{j=0}^{k} a_j/N^j| \leq C_k(F)/N^{k+1}$.

**No convergence of the 1/N series needed:** at $N = 100$, the
leading-order error is $\leq C/100$. The two-term approximation gives
$\leq C'/10000$. This is rigorous regardless of whether $\sum a_k/N^k$
converges.

### The nature of the 1/N series

The 1/N expansion $\sum_k a_k(F)/N^k$ is a formal power series.
Its convergence properties:

| Dimension | Convergence | Why |
|---|---|---|
| $d = 2$ (P($\phi$)$_2$) | **Possibly convergent** | Super-renormalizable, no renormalons, no instantons, convex $S_{\text{eff}}$ |
| $d = 3$ | Likely asymptotic | Renormalon-like effects, but Borel summable |
| $d = 4$ | Asymptotic (zero radius) | Factorial growth from renormalons |

For $d = 2$: the convexity of $S_{\text{eff}}$ and the absence of
tunneling (single phase at fixed $\lambda > 0$) suggest the series
might converge. But this is **not proved**. Even without convergence,
the Brascamp-Lieb remainder bounds give rigorous control at each
truncation order.

### Correction: Schwinger functions are NOT polynomial in N

The earlier claim that the Schwinger functions are polynomials in $N$
was **wrong**. Even on a finite lattice, $Z(N)$ involves
$\text{vol}(S^{N-1}) = 2\pi^{N/2}/\Gamma(N/2)$, which is
transcendental in $N$.

What IS true:
- At each finite order in $\lambda$: the Wick contractions produce
  polynomials in $N$ (Brauer algebra combinatorics)
- The full nonperturbative Schwinger functions are power series in
  $1/N$, not polynomials
- The power series has controlled remainders (Laplace / Brascamp-Lieb)

The rigorous chain:

1. **pphi2 at each $N$:** measure $\mu_N$ exists, bounds polynomial
   in $N$ (Nelson estimate)
2. **$\sigma$-integral well-defined:** $\nu_N$ on invariant field
   with log-concave density $\exp(-N/2 \cdot S_{\text{eff}})$
3. **Brascamp-Lieb:** $\text{Var}_N(F) \leq C(F)/N$
4. **Laplace expansion with remainder:** $|\langle F \rangle_N - \sum_{j \leq k} a_j/N^j| \leq C_k/N^{k+1}$
5. **Continuum limit preserves bounds:** all estimates uniform in
   lattice spacing $a$ (from pphi2 tightness)

### The rigorous FRG theorem (corrected)

**Theorem** (target for pphi2N). *For the O(N) P($\phi$)$_2$ theory
on $T^2_L$ with interaction $P(\phi \cdot \phi)$:*

1. *The lattice invariant-field measure $\nu_{N,a}$ exists for each
   $a > 0$ and integer $N \geq 1$. Its log-density $V_a(\sigma; N)$
   has a $1/N$ asymptotic expansion with controlled remainders.*

2. *The lattice RG flow $V_a \to V_{2a}$ converges to the Wetterich
   LPA equation as $a \to 0$, with convergence rate $O(a^2)$.*

3. *At leading order in $1/N$: the flow is exactly solvable, the
   saddle-point $\sigma^*$ satisfies the gap equation, and the error
   is bounded: $|V_a(\sigma; N) - V_a^{N=\infty}(\sigma)| \leq C/N$
   (Brascamp-Lieb).*

This would be the **first rigorous derivation of the Wetterich equation
from an actual QFT construction** — deriving the FRG as a consequence
of measure convergence, rather than assuming it from path integral
manipulations.

### Application: rigorous mass gap at large but finite N

The Brascamp-Lieb bounds on the $\sigma$-measure can prove the mass
gap for the O(N) NLSM in $d = 2$ at large but finite $N$:

1. **At $N = \infty$:** the gap equation gives $m(\infty) > 0$
   (rigorously: Kupiainen 1980). This is the saddle-point mass.

2. **At finite $N$:** Brascamp-Lieb gives
   $|m(N) - m(\infty)| \leq C'/N$ where $C'$ is computable from
   $S'''_{\text{eff}}$ and $S''''_{\text{eff}}$.

3. **For $N \geq N_0 = \lceil C'/m(\infty) \rceil$:** the mass gap
   $m(N) \geq m(\infty) - C'/N > 0$.

| Theory | Mass gap status | What $1/N$ adds |
|---|---|---|
| P($\phi$)$_2$ | All $N \geq 1$ (pphi2, Jentzsch) | Quantitative: $m(N) = m(\infty) + O(1/N)$ |
| **O(N) NLSM, $d = 2$** | **$N = \infty$ only (Kupiainen)** | **$m(N) > 0$ for $N \geq N_0$ — new** |
| O(N) NLSM, $N = 3$ | Not proved | Would need $N_0 \leq 3$ (unlikely from $1/N$ alone) |

The NLSM result would be **genuinely new**: the Jentzsch approach
(positivity-improving transfer matrix) that pphi2 uses for P($\phi$)$_2$
doesn't apply to the NLSM (compact target, different transfer matrix
structure). The $\sigma$-measure approach via Brascamp-Lieb gives a
different route that works at large $N$.

The threshold $N_0$ depends on the coupling and lattice spacing.
At weak coupling: $N_0$ is exponentially large (the mass is
nonperturbatively small). At moderate coupling: $N_0$ could be
$O(10)$-$O(100)$, giving a concrete rigorous result.

Even $N_0 = 100$ would be new: **rigorous mass gap for O(100) NLSM
in 2D.** Nobody has this by any other method.

### Caveats: Goldstone modes and the critical point

**Critical point.** For P($\phi$)$_2$ at the critical coupling:
$\sigma^* \to 0$, the mass gap vanishes, and the Brascamp-Lieb
bound $C'/N$ is useless (can't prove positivity when the limit is
zero). The mass gap proof only works in the **massive regime**
(positive bare mass, away from criticality).

**Goldstone modes.** For $N \geq 2$ in $d = 2$:

1. The saddle point gives $(N-1)$ Goldstone modes with mass
   $m_G = \sqrt{\sigma^*}$, which dominates the low-energy spectrum.

2. Mermin-Wagner: continuous symmetry can't break in $d = 2$. If
   the saddle point selects a "broken" phase, the Goldstone
   fluctuations (which are $O(1)$, not small) restore the symmetry.
   The $1/N$ expansion around a broken saddle is WRONG in $d = 2$.

3. For the symmetric phase (positive bare mass): $\sigma^* > 0$, all
   modes massive, $1/N$ expansion valid. For the NLSM: the symmetric
   saddle gives $\sigma^* = $ dynamically generated mass$^2 > 0$, but
   this is exponentially small at weak coupling.

| Regime | $\sigma^*$ | $1/N$ valid? | Mass gap provable? |
|---|---|---|---|
| P($\phi$)$_2$, massive | $> 0$ (large) | Yes | Yes (but pphi2 already has it) |
| P($\phi$)$_2$, critical | $\to 0$ | Breaks down | No (gap = 0) |
| NLSM, weak coupling | $> 0$ (exp. small) | Formally | $N_0$ exponentially large |
| $N = 2$, BKT regime | Subtle | No | No (algebraic decay) |

### The clean argument: $\sigma$-concentration $\Rightarrow$ mass gap

The $\sigma$-field gives a mass to ALL $\phi$-components simultaneously
(radial and Goldstone). The argument:

**Step 1 (conditional gap).** For any $\sigma$ with $\sigma(x) \geq
\sigma_{\min} > 0$ everywhere: the conditional $\phi$-measure
(Gaussian with covariance $(-\Delta + \sigma)^{-1}$) has mass gap
$\geq \sqrt{\sigma_{\min}}$ for all $N$ components.

**Step 2 ($\sigma$-concentration).** From Brascamp-Lieb:
$\text{Var}(\sigma(x)) \leq C/N$. In $d = 2$, Sobolev embedding
$H^1 \hookrightarrow L^\infty$ (with log correction) gives:

$$\|\sigma - \sigma^*\|_{L^\infty} \leq \frac{C'\sqrt{\log|\Lambda|}}{\sqrt{N}} \quad \text{with high probability}$$

**Step 3 (combine).** For $N > C'^2 \log|\Lambda| / \sigma^{*2}$:
$\sigma(x) \geq \sigma^*/2 > 0$ everywhere, so mass gap
$\geq \sqrt{\sigma^*/2}$.

The Goldstone modes are controlled because $\sigma$ gives a COMMON
(scalar) mass to ALL modes — it's direction-independent.

**The threshold:**

$$N_0 \sim C^2 \log|\Lambda| / \sigma^{*2}$$

Only logarithmic in the volume — much better than previous estimates.

| Theory | $\sigma^*$ | $N_0$ |
|---|---|---|
| P($\phi$)$_2$, massive | $m_0^2 + O(\lambda N)$ | $\sim C^2 \log|\Lambda|/m_0^4$ (small) |
| NLSM, moderate coupling | $\sim \Lambda^2 \cdot O(1)$ | $\sim C^2 \log|\Lambda|$ (reasonable) |
| NLSM, weak coupling | $\sim \Lambda^2 e^{-4\pi/(g^2 N)}$ | exponentially large |

For P($\phi$)$_2$ in the massive regime: a clean quantitative mass
gap at large $N$ with explicit constants. For the NLSM at moderate
coupling: a genuine new result ($N_0 \sim O(10)$-$O(100)$).

### The TRG connection

The TRG coarse-graining IS a discrete version of the FRG:
- The lattice spacing $a$ plays the role of $1/k$ (inverse RG scale)
- The TRG tensor at level $n$ encodes $V_k(\sigma)$ at $k = \Lambda/2^n$
- The SVD truncation approximates the exact Wetterich flow
- The bond dimension $\chi$ controls the truncation order

The invariant field $\sigma(x,y) = \phi(x) \cdot \phi(y)$ IS the
"bond field" in TRG language. The RG flow of $V_k(\sigma)$ IS the
TRG flow of the bond-space effective action. This connection makes
the TRG ↔ FRG correspondence precise.
