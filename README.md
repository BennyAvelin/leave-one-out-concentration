# LOOConcentration

A Lean 4 formalization of the manuscript *Concentration inequalities for
leave-one-out cross-validation* by **Benny Avelin and Lauri Viitasaari**
([arXiv:2211.02478](https://arxiv.org/abs/2211.02478)). It proves concentration
and moment bounds for the difference between prediction risk and its
leave-one-out estimate, under gradient stability and a log-Sobolev inequality
for the observation law.

The library also includes estimator applications, a uniform-deletion result,
and model-selection extensions. It is built on
[Mathlib](https://github.com/leanprover-community/mathlib4).
The precise source version and correspondence limits are recorded in
[Verification](VERIFICATION.md). The older published preprint was never
formalized.

## The main results

Let $`D=(Z_1,\ldots,Z_N)`$ be $`N\ge2`$ independent observations with law $`\mu`$,
and let $`\ell(D,z)`$ denote the loss of the estimator trained on $`D`$, evaluated
at a test observation $`z`$. Write

```math
\begin{aligned}
\widehat R_{\mathrm{LOO}}(D)&=\frac1N\sum_{i=1}^N\ell(D^{(-i)},Z_i),\\
R(D)&=\mathbb{E}[\ell(D,Z)\mid D],\\
H(D)&=R(D)-\widehat R_{\mathrm{LOO}}(D).
\end{aligned}
```

where $`Z`$ is an independent test observation. The formal risk is an $`L^1`$
conditional-expectation class with a proved characterization and uniqueness
theorem. Probabilities and norms below use the sample law $`\mu^{\otimes N}`$.
Let $`C`$ be the finite variational log-Sobolev constant of $`\mu`$, and
$`M_2=\mathbb{E}|Z|^2`$.

### Theorem 1: the Lipschitz case

When the training-data gradient bound has no linear-growth term and the
mean fitted loss is $`c`$-Lipschitz in the test observation, the error has
Gaussian tails. If $`\delta_1(N-1,z)\le a`$ for $`\mu`$-almost every $`z`$, set

```math
s=a+\frac{c}{\sqrt N}+\mathbb{E}\delta_1(N,Z).
```

For every $`t>0`$,

```math
\mathbb{P}\bigl(|H|>\delta_3(N)+t\bigr)
\le2\exp\!(-\frac{t^2}{2Cs^2}).
```

The factor two is omitted for either one-sided tail. When $`Cs^2=0`$, the
formal right-hand side is zero. The declaration also includes an integrated
tail bound without the uniform bound $`a`$, and an eventual bound of the form
$`3N\exp(-c_0\varepsilon^2N)`$ under uniform $`N^{-1/2}`$ stability rates and uniformly bounded
mean-loss Lipschitz constants.

### Theorem 2: general concentration

For gradient bounds with linear growth, define the rate, on the branch
$`C>0`$, $`b>0`$ and $`a^2+2b^2rM_2>0`$, by

```math
\theta_r(t;a,b)=\exp\![-\min\!\{
\frac{t^2}{8C(a^2+2b^2rM_2)},\frac{t}{8Cb}
\}].
```

For $`\varepsilon>3\delta_3(N)`$, each of
$`\mathbb{P}(H>\varepsilon)`$ and $`\mathbb{P}(-H>\varepsilon)`$ is at most

```math
\begin{aligned}
&N\,\mathbb{E}\theta_{N-1}\!(
\frac\varepsilon3;\delta_1(N-1,Z),\delta_2(N-1,Z))\\
&\quad+\theta_N\!(\frac\varepsilon3;\frac c{\sqrt N},\frac dN)\\
&\quad+\theta_N\!(\frac\varepsilon3-\delta_3(N);
\mathbb{E}\delta_1(N,Z),\mathbb{E}\delta_2(N,Z)).
\end{aligned}
```

If $`\delta_1(N-1,z)\le a`$ and $`\delta_2(N-1,z)\le b`$ almost everywhere,
the first term can be replaced by $`\theta_{N-1}(\varepsilon/3;a,b)`$.
The [rate definition](LOOConcentration/formal/LOOConcentrationRevision/Frozen/Definitions/ThetaRate.lean)
also specifies every zero-constant branch, including the Gaussian case $`b=0`$.

### Corollary 1: moment bounds

For $`p\ge2`$, assume $`\delta_1(N-1,\cdot)`$ and
$`\delta_2(N-1,\cdot)`$ belong to $`L^p(\mu)`$. Put
$`Q_r=\sqrt{rM_2+C(p-2)}`$ and

```math
\begin{aligned}
B_p=\sqrt{C(p-1)}\Bigl(&\|\delta_1(N-1,\cdot)\|_p
+Q_{N-1}\|\delta_2(N-1,\cdot)\|_p\\
&+\frac c{\sqrt N}+\frac dN Q_N
+\mathbb{E}\delta_1(N,Z)+Q_N\mathbb{E}\delta_2(N,Z)\Bigr).
\end{aligned}
```

Then $`\|H-\mathbb{E}H\|_p\le B_p`$ and
$`\|H\|_p\le\delta_3(N)+B_p`$. At $`p=2`$ this also gives
$`\mathrm{Var}(H)\le B_2^2`$.

### Theorem 3: concentration on a large set

Let $`H`$ be measurable, $`\|H\|_2\le B`$ and $`|\mathbb{E}H|\le\delta`$.
Suppose $`H`$ is $`L_K`$-Lipschitz on a measurable set $`K`$ of positive sample
probability, and write $`q=\mathbb{P}(D\notin K)<1`$. Define

```math
\eta_K=B\sqrt{\frac q{1-q}},\qquad
C_K=3\cdot2^{12}e^2C\log\!(\frac e{1-q}).
```

For $`\varepsilon>\delta+\eta_K`$,

```math
\mathbb{P}(|H|>\varepsilon)
\le q+2\exp\!(-\frac{(\varepsilon-\delta-\eta_K)^2}
{2C_KL_K^2}).
```

Each one-sided bound has factor one in place of two. The exponential term
is defined to be zero when $`C_KL_K^2=0`$. This theorem applies to any $`H`$
satisfying these assumptions, including the leave-one-out error.

## The hypotheses

The first three results use
[`StandingAssumption`](LOOConcentration/formal/LOOConcentrationRevision/Frozen/Definitions/StandingAssumption.lean).
It requires a finite log-Sobolev constant, a finite second moment, measurable
and integrable losses, and locally Lipschitz dependence on the training data.
For a training sample of size $`r`$, the gradient satisfies

```math
|\nabla_D\ell(D,z)|\le\delta_1(r,z)+\delta_2(r,z)|D|.
```

This holds for $`\mu`$-almost every test observation $`z`$, and then for
Lebesgue-almost every training dataset $`D`$. The nonnegative stability rates
vanish with sample size, and $`\delta_3(N)`$ controls the difference between
the expected full-sample risk and each expected deleted-sample loss.
The mean fitted loss is locally Lipschitz, with gradient bounded by
$`c+d|z|`$ almost everywhere. The exact integrability clauses and order of
quantifiers are part of the Lean statements.

Theorem 3 instead assumes a finite log-Sobolev constant and second moment,
and the explicit measurability, moment, bias and large-set Lipschitz
conditions stated above.

## How the proof works

The proofs separate training-data fluctuations, fluctuations in the test
observation, and the delete-one bias. Tensorization of the log-Sobolev
inequality controls the product sample law. Gradient bounds give moment and
exponential estimates; a union bound combines the deleted-sample terms.
Uniform stability bounds yield the sharper first term in Theorem 2.

The large-set result controls concentration under the law conditioned on $`K`$.
The $`L^2`$ bound controls the change in mean, producing $`\eta_K`$, and the
probability outside $`K`$ contributes the additive term $`q`$.

## The Lean statements

The four main results use the namespace `LOOConcentration.Revision`:

| Manuscript result | Lean declaration |
| --- | --- |
| Theorem 1: Lipschitz concentration | [`simplifiedConcentration`](LOOConcentration/formal/LOOConcentrationRevision/Frozen/Results/SimplifiedConcentration.lean) |
| Theorem 2: general concentration | [`mainConcentration`](LOOConcentration/formal/LOOConcentrationRevision/Frozen/Results/MainConcentration.lean) |
| Corollary 1: centered moments | [`looMoments`](LOOConcentration/formal/LOOConcentrationRevision/Frozen/Results/LooMoments.lean) |
| Theorem 3: large-set concentration | [`dataDependentConcentration`](LOOConcentration/formal/LOOConcentrationRevision/Frozen/Results/DataDependentConcentration.lean) |

The Lean indexing uses $`N=n+2`$. The estimator `T n` trains on $`n+1`$
observations; `T (n + 1)` trains on the full sample. The Gaussian OLS
application is `LOOConcentration.olsConcentration`. Estimator and
model-selection extensions use `LOOConcentration.Manuscript`.

```lean
import LOOConcentrationRevision
import LOOConcentrationManuscript
import LOOConcentrationManuscript.Supplementary
import LOOConcentrationManuscript.ModelSelection
```

## Guarantees

- **Complete production proofs.** All 560 production modules build, with no
  `sorry` or custom `axiom` in the library.
- **Axiom audit.** The 86 audited exports and four challenge solutions depend
  only on `propext`, `Classical.choice` and `Quot.sound`.
- **Exact exercises.** The four challenges have the same theorem headers as
  the library results; their elaborated types are checked against them.
- **Pinned dependencies.** Lean `v4.33.1`, Mathlib at
  `0df444a360eaa60ab8c11dca51a86af692955474`, and pinned transitive packages.

The library proves the Lean declarations. Whole-manuscript correspondence
is not certified: three contextual source rulings remain pending, and
simulation material and the bounded-data/no-LSI remark are excluded.
[Verification](VERIFICATION.md) records the scope and source limitations.

## Build and check

Install [Elan](https://github.com/leanprover/elan), then run from the
repository root:

```sh
cd LOOConcentration/formal
lake exe cache get
python3 scripts/ci.py
```

The checker builds the complete library, verifies source and dependency pins,
audits theorem types and axioms, and runs the challenge regressions.
Fetch the pinned dependency caches first; CI stops if it observes upstream
compilation. See [Verification](VERIFICATION.md) for individual checks and
the fresh-build procedure.

## Theorem challenges

[`Challenge.lean`](LOOConcentration/formal/challenges/Challenge.lean) contains
the four main results with intentional exercise holes.
[`Solution.lean`](LOOConcentration/formal/challenges/Solution.lean) supplies
reference proofs. These files are separate from the production library; the
challenge imports definitions and prerequisites without importing result proofs.

The local comparator checks exact theorem types and allowed axioms. It is a
project-specific exercise format. See the
[challenge guide](LOOConcentration/formal/challenges/README.md) for commands,
alternative solutions and the comparator's limits.

## Authors and license

The mathematical paper and project attribution credit **Benny Avelin and
Lauri Viitasaari**. The formalization was developed under Benny Avelin's
supervision through paper-guided, LLM-assisted proof development and separate
review.

Project code and documentation use the [Apache License 2.0](LICENSE), with
attribution in [NOTICE](NOTICE). The manuscript retains its authors' copyright.
Dependencies retain their own licenses; see [dependency attribution](DEPENDENCIES.md).
