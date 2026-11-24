# The limit shape of uniform random antichains, formalized in Lean 4

This repository contains machine-checked proofs for

> Andrew Elvey Price and Minjae Park, **[The limit shape of uniform random antichains in \[0,1\]ᵈ](paper/main.pdf)**, [arXiv:2611.30371](https://arxiv.org/abs/2611.30371)

The linked PDF presents the statements and outlines the verified proofs.

Fix $`d\ge 2`$ and sample $`n`$ independent uniform points in the cube. They form an antichain if no point is strictly smaller than another in every coordinate. The paper determines the logarithmic probability of this event, the shape and empirical distribution of the sample conditioned on it, and the limiting permuton of the associated pattern-avoiding permutations.

## Main results

**Counting (Theorem 1.1).** If $`a_n`$ is the probability of the antichain event, then there is a finite constant $`\beta_d`$ such that

```math
\log a_n = -\frac{n}{d-1}\log n + \beta_d n + o(n).
```

The proof specializes the weighted Gaussian partition estimate of Proposition 1.3 to zero weights. The counting statement is [`Antichain.antichain_counting_source_direct`](Antichain/DirectSourceEndpoints.lean#L38) and the weighted estimate is [`Antichain.weighted_volume_source_direct`](Antichain/DirectSourceEndpoints.lean#L23).

**Shape (Theorem 1.2).** The conditioned sample cloud concentrates exponentially in Euclidean Hausdorff distance around the closure of

```math
\mathcal{S}_d=\bigl\lbrace x\in(0,1)^d : \sum_{i=1}^d\Phi^{-1}(x_i)=0\bigr\rbrace,
```

where $`\Phi`$ is the standard normal CDF. The Lean statement is [`Antichain.euclidean_shape_exponential_concentration_direct`](Antichain/DirectSourceEndpoints.lean#L51).

**Empirical law (Theorem 2.1).** Let $`\mathbb{P}_n`$ be the law of the sample $`X^{(1)},\ldots,X^{(n)}`$ conditioned on the antichain event. Let $`Y=(Y_1,\ldots,Y_d)`$ have independent standard normal coordinates and let $`\bar Y=d^{-1}\sum_i Y_i`$. The empirical and limiting measures are

```math
\widehat\mu_n=\frac{1}{n}\sum_{k=1}^n\delta_{X^{(k)}},\qquad
\mu^\ast=\mathrm{Law}\!\bigl(\Phi\!\bigl(\sqrt{\frac{d}{d-1}}\,(Y-\bar{Y}\mathbf{1})\bigr)\bigr),
```

with $`\Phi`$ acting coordinatewise. The vector inside $`\Phi`$ has zero coordinate sum and standard normal marginals, so $`\mu^\ast`$ is supported on $`\overline{\mathcal S_d}`$ and has uniform marginals. For every open neighborhood $`U`$ of $`\mu^\ast`$ in the weak topology on probability measures on $`[0,1]^d`$, there is $`\alpha=\alpha(d,U)>0`$ such that, for all sufficiently large $`n`$,

```math
\mathbb{P}_n(\widehat\mu_n\notin U)\le e^{-\alpha n}.
```

In particular, for every Borel set $`B\subseteq[0,1]^d`$ with $`\mu^\ast(\partial B)=0`$, where the boundary is taken in the closed cube,

```math
\widehat\mu_n(B)=\frac{1}{n}\sum_{k=1}^n\mathbf{1}_B(X^{(k)})\longrightarrow\mu^\ast(B)
\quad\text{in }\mathbb{P}_n\text{-probability}.
```

The two conclusions are [`Antichain.closed_cube_empirical_source_direct`](Antichain/DirectSourceEndpoints.lean#L58) and [`Antichain.closed_cube_continuity_set_in_probability_direct`](Antichain/DirectSourceEndpoints.lean#L71).

**Rank permuton (Theorem 6.2).** Order the conditioned sample by its first coordinate and write $`\pi_i(k)`$ for the rank of the $`i`$th coordinate of the $`k`$th point. Then $`\pi_1`$ is the identity, and $`(\pi_1,\ldots,\pi_d)`$ is uniform over the $`d`$-permutations avoiding $`(12,\ldots,12)`$. Set

```math
u_{r,n}=\frac{r-\tfrac{1}{2}}{n},\qquad
R^{(k)}=\bigl(u_{\pi_i(k),n}\bigr)_{i=1}^d,\qquad
\widehat\mu_n^{\mathrm{rk}}=\frac{1}{n}\sum_{k=1}^n\delta_{R^{(k)}}.
```

The rank-box permuton $`\mu_n^{\mathrm{rk}}`$ spreads each mass $`1/n`$ uniformly over the cube of side $`1/n`$ centered at $`R^{(k)}`$. Each coordinate rank interval occurs once, giving the spread measure uniform marginals. For every open weak neighborhood $`U`$ of $`\mu^\ast`$, there is $`\alpha=\alpha(d,U)>0`$ such that, for all sufficiently large $`n`$,

```math
\mathbb{P}_n\!\bigl(\widehat\mu_n^{\mathrm{rk}}\notin U
\;\text{or}\;\mu_n^{\mathrm{rk}}\notin U\bigr)\le e^{-\alpha n}.
```

The joint bound is [`Antichain.rank_permuton_source_hoeffding`](Antichain/RankLimitsHoeffding.lean#L20). The uniform marginals of the spread measure are proved in [`Antichain.closedRankBoxProbability_coordinate_uniform`](Antichain/RankPermuton.lean#L291).

## Scope and correspondence with the paper

The [paper coverage table](formalization/PAPER_COVERAGE.md) maps the paper’s proved results to their Lean declarations and source lines. To compare statements, read the declaration above `:=` and check the objects it uses against the [definition correspondence](formalization/CORRESPONDENCE.md). The [proof comparison](formalization/REVISION_REVIEW.md) explains where Lean expands details of the written arguments.

## Repository layout

| Path | Contents |
|---|---|
| [Antichain/](Antichain/) and [Antichain.lean](Antichain.lean) | The proof library and its root import |
| [Antichain/DirectSourceEndpoints.lean](Antichain/DirectSourceEndpoints.lean) | Counting, weighted limits, shape, and empirical laws stated for the paper’s model |
| [formalization/](formalization/) | Paper-to-Lean links, proof correspondence, and the [proof guide](formalization/PROOF_GUIDE.md) |
| [paper/](paper/) and [source/](source/) | The annotated companion and the original manuscript sources |
| [release/](release/) | Audit evidence, frozen declaration types, and the [source index](release/theorem-source-index.json) |

## Build and check

Install Git, Python 3.10 or later, and [elan](https://github.com/leanprover/elan). Run these commands from the repository root.

```sh
lake exe cache get
python verify.py
python scripts/check_release.py
```

The project uses Lean 4.24.0 and Mathlib at `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. The verifier rebuilds the library with the pinned toolchain and checks the complete types and transitive axioms of its declarations. The only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. The whole-project build and exhaustive type and axiom audit passed at `2026-11-19T14:19:55.810750+00:00` and covered 169 production modules plus the root, 3,151 theorem declarations and 3,708 declarations in total. Every source and audit input is frozen by its exact hash. The release checker validates the packaged manuscript, proof mappings, and audit evidence.

## Authors and citation

Cite Andrew Elvey Price and Minjae Park, *The limit shape of uniform random antichains in \[0,1\]ᵈ*, together with this repository if you use the formalization. The paper’s AI disclosure describes how the project’s Lean proofs were prepared and how the authors reviewed the main statements. The code is [MIT licensed](LICENSE). The [notices](NOTICE.md) describe the manuscript and dependency rights.
