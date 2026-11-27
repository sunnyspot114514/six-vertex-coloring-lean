# Six-vertex coloring lemma

[![Verify](https://github.com/sunnyspot114514/six-vertex-coloring-lean/actions/workflows/verify.yml/badge.svg)](https://github.com/sunnyspot114514/six-vertex-coloring-lean/actions/workflows/verify.yml)

[中文说明](README.zh-CN.md) · [Elementary proof](docs/proof.md) · [Lean theorem](SixVertex/Coloring.lean)

**Any triangle-free simple graph with at most six vertices admits a vertex coloring that avoids matching both endpoints to the color of their edge, for every red/blue edge coloring.**

For example, a red edge may connect a red vertex to a blue vertex, or two blue vertices; it must not connect two red vertices. The analogous rule holds for blue edges.

This repository packages a short human-readable proof, an independently written exhaustive checker, and a standalone Lean formalization of this finite lemma.

## New arithmetic result: the 65-prime-factor case of A245211

For the weighted proper-divisor sum

$$
a(n)=\sum_{\substack{d\mid n\\d<n}} d\,\tau(d),
$$

where $\tau(d)$ counts positive divisors, the new theorem states:

**Every squarefree integer with exactly 65 distinct prime factors satisfies $a(n)\ne n$. There is no upper bound on $n$.**

The [H1 single-file proof](A245211/count65/proofs/OeisA245211.conjecture.R2.H3.R1.H1.lean) has the exact target

```lean
∀ n : ℕ, Squarefree n → n.primeFactors.card = 65 →
  OeisA245211.a n ≠ n
```

The proof reduces a hypothetical fixed point to a cycle of large primes and uses

$$
2^{65}+1=3\cdot11\cdot131\cdot2731\cdot409891\cdot7623851.
$$

All listed factors except 3 are congruent to 1 modulo 5. After rotating the factor 3 to the first position and applying the proved projection lemma, a single modular specification remains. Its forced starting residue is 1, and the next two prime residues are $1\to1\to0\pmod5$, contradicting primality and the lower bound on those primes. The finite calculation is a kernel certificate after this mathematical reduction; it imposes no size bound on the original integer.

The accompanying [proposed reduction](A245211/count65/reductions/OeisA245211.conjecture.R2.H3.R1.lean) splits the existing `R2.H3` into this exact 65-factor case and the remaining squarefree cases with **odd, non-prime-power factor counts at least 67**. That remaining statement is open in this work. **This does not solve all of H3 or the full OEIS conjecture.** See the [detailed proof and verification notes in Chinese](A245211/count65/README.zh-CN.md).

### A245211 verification and publication status

Both independent GitHub CI runs succeeded:

| Result | Successful CI run | Source commit |
|---|---|---|
| New 65-factor case and its proposed H3 reduction | [46066283100](https://github.com/sunnyspot114514/six-vertex-coloring-lean/actions/runs/46066283100) | [`109233726473`](https://github.com/sunnyspot114514/six-vertex-coloring-lean/commit/1092337264737c2b8ffc771cb1e1edea6fd28717) |
| Independent implementation of the existing R2.H2 result | [46064959548](https://github.com/sunnyspot114514/six-vertex-coloring-lean/actions/runs/46064959548) | [`b8dd8c8e5f72`](https://github.com/sunnyspot114514/six-vertex-coloring-lean/commit/b8dd8c8e5f726ab70812fadb20c39289b2e79444) |

The original upstream checker returned **`accepted` for all three submissions**: H2, the new reduction, and H1. Each axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`.

The [count65 workflow](.github/workflows/a245211-count65.yml) separately checks the reduction and H1 using the unmodified upstream checker. It preserves the per-submission time limit and axiom audit, and saves the verdicts and source hashes. The [H2 workflow](.github/workflows/a245211.yml) is separate.

**The new reduction and 65-factor proof are published in this repository only. No upstream pull request has been submitted or merged for these two files.** Upstream submission would require the reduction to be accepted before its H1 proof is submitted.

### Earlier H2 result: independent implementation, with prior work credited

The [H2 implementation](A245211/submission/OeisA245211.conjecture.R2.H2.lean) covers squarefree integers whose distinct-prime-factor count is one of
`15, 21, 33, 35, 39, 45, 51, 55, 57, 63`, again without bounding the integer itself. These are the odd counts between 3 and 64 that are not positive powers of a prime.

**MakisChristou's [upstream PR #9600](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9600) had already solved and merged H2 before this implementation completed verification.** Our implementation is independent and reproducible; we claim no first solution and are not submitting a duplicate H2 proof upstream. Its [Chinese documentation](A245211/README.zh-CN.md) explains the cycle reduction, modular certificates, and scope.

## Additional finite audit: consecutive cube-full integers

[![Cube-full audit](https://github.com/sunnyspot114514/six-vertex-coloring-lean/actions/workflows/cube-full.yml/badge.svg)](https://github.com/sunnyspot114514/six-vertex-coloring-lean/actions/workflows/cube-full.yml)

The [additional audit](docs/cube-full-audit.md) proves that no integer `1 ≤ n ≤ 100000` has both `n` and `n + 1` cube-full. This refutes the bounded hypothesis `Erdos366.erdos_366.variants.weaker.R1.H1` proposed in the upstream reduction. The result includes a [Lean certificate](Additional/CubeFull.lean) and an independent arithmetic checker. The unbounded Erdős #366 question is outside this result's scope.

## Why it works

Every triangle-free graph on at most six vertices is either bipartite or becomes bipartite after deleting one edge. A non-bipartite example must contain a chordless five-cycle. There is at most one vertex outside that cycle, and triangle-freeness permits at most two neighbors on it. Inspecting those possibilities proves the one-edge deletion claim.

Properly color the remaining bipartite graph. If the deleted edge would violate the requested condition, swap every vertex color. Its endpoints are repaired, and all other edges still have differently colored endpoints. See the [complete structural proof](docs/proof.md).

## Verification

The Python checker exhausts all labeled simple graphs on six vertices:

| Class | Count |
|---|---:|
| All graphs | 32,768 |
| Triangle-free graphs | 5,789 |
| Already bipartite | 5,177 |
| Require exactly one edge deletion | 612 |
| Graph/edge-coloring pairs verified | 294,987 |
| Counterexamples | 0 |

The Lean proof checks the finite graph property with kernel reduction, connects the encoding to `SimpleGraph`, and proves the final statement for every `k ≤ 6`. Python output is not an axiom or input trusted by the Lean theorem.

CI builds the source, replays the project's modules with `leanchecker`, and inspects the final theorem's axiom dependencies. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. The workflow badge above is the live verification result for this repository.

### Reproduce

Install [elan](https://github.com/leanprover/elan), then run:

```bash
python3 scripts/check_exhaustive.py
lake update
lake exe cache get
lake build
lake env leanchecker SixVertex
lake env lean Check.lean
```

Lean is pinned to **4.33.1**. Mathlib is pinned to commit **0df444a360eaa60ab8c11dca51a86af692955474** (the v4.33.1 release).

## Files

| File | Purpose |
|---|---|
| `docs/proof.md` | Complete elementary proof, in English |
| `docs/proof.zh-CN.md` | Complete elementary proof, in Chinese |
| `SixVertex/Finite.lean` | Kernel-checked finite graph calculation |
| `SixVertex/Coloring.lean` | Graph encoding and the final edge-color avoidance theorem |
| `scripts/check_exhaustive.py` | Independent exhaustive verification with ordinary Python |
| `Check.lean` | Final theorem type and axiom report |
| `.github/workflows/verify.yml` | Reproducible verification workflow |

## Context and attribution

The target is the finite hypothesis **H2** from the [R1 reduction of an Erdős #151 variant](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4050), contributed by **dk8827** to Left to Solve.

While preparing this repository, we checked the current upstream GitHub state and found that **Salofe's [PR #5331](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5331)** had already been accepted and merged on **27 November 2026 at 11:22:31 UTC**. The site's earlier “open step” listing was stale. That formalization also uses a finite graph check followed by a global color swap. It is the prior accepted formalization; this repository claims no first-solution credit.

Prepared for **sunnyspot114514** with assistance from **ChatGPT**.

### Scope

This is a small, fully specified graph lemma and a reproducibility exercise. **It does not solve Erdős Problem 151**, its general `cliqueFree_four` variant, or the other hypotheses in the upstream reduction. Its human proof uses the five-cycle structure; the Lean implementation verifies the corresponding finite graph property computationally.


