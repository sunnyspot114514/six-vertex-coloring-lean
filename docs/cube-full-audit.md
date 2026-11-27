# A bounded audit of consecutive 3-full integers

[中文版](cube-full-audit.zh-CN.md)

**Result.** For every integer $n$ with $1\le n\le100000$, at least one of $n,n+1$ is not 3-full. This refutes the finite step `Erdos366.erdos_366.variants.weaker.R1.H1` in the inspected upstream reduction. The unbounded existence question remains outside the scope of this result. We make no claim of mathematical priority.

The Lean development is [Additional/CubeFull.lean](../Additional/CubeFull.lean). An independent numerical audit is [scripts/check_cube_full.py](../scripts/check_cube_full.py). The discussion below distinguishes the theorem proved by the Lean development from the additional numerical statistics produced by Python.

## 1. The exact statement being audited

The upstream reduction defines the following proposition:

```lean
def H1 : Prop :=
  ∃ n : ℕ, 0 < n ∧ n ≤ 100000 ∧ Nat.Full 3 n ∧ Nat.Full 3 (n + 1)
```

Thus the upper bound applies to the **first** member of the pair; checking it requires the integers through $100001$. The source is [the Erdos366 reduction, snapshot 37c14b8](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/37c14b8ac3fd1f4f30d041fdb05c4b084078ab25/reductions/Erdos366.erdos_366.variants.weaker.R1.lean).

In Formal Conjectures, the definition of fullness is:

```lean
def Nat.Full (k : ℕ) (n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ k ∣ n
```

For positive $n$, being 3-full means that every prime appearing in its factorization has exponent at least three. The integer $1$ satisfies the condition because it has no prime factors. The definition also regards $0$ as full, but the audited statement explicitly requires $n>0$. See [the definition of `Nat.Full`, snapshot 9097e2f](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjecturesForMathlib/Data/Nat/Full.lean).

Our standalone Lean file uses the equivalent predicate

```lean
def IsCubeFull (n : Nat) : Prop :=
  ∀ p : Nat, p.Prime → p ∣ n → p ^ 3 ∣ n
```

`CubeFull.isCubeFull_iff_primeFactors` proves its equivalence to the prime-factor formulation used by `Nat.Full 3`, including $n=0$. Consequently, the theorem `CubeFull.refutesBoundedExistence` has exactly the mathematical content of $\neg H1$.

## 2. A complete finite enumeration

Every positive 3-full integer has a unique representation

$$
n=a^3b^4c^5,
\qquad a,b,c\ge1,
$$

where $b$ and $c$ are squarefree and $\gcd(b,c)=1$. The integer $a$ may share prime factors with either $b$ or $c$.

To prove this, consider a prime exponent $e\ge3$ in $n$. If $e\equiv0\pmod3$, put the whole exponent into $a^3$. If $e\equiv1\pmod3$, then $e\ge4$: put one copy of the prime into $b$ and the remaining exponent $e-4$ into $a^3$. If $e\equiv2\pmod3$, then $e\ge5$: put one copy into $c$ and the remaining exponent $e-5$ into $a^3$. This constructs the representation. Conversely, a prime in such a product occurs with exponent $3u+4v+5w$, where $v,w\in\{0,1\}$ and $vw=0$, so every positive exponent is at least three. Its residue modulo three determines $v,w$ uniquely, and then determines $u$.

For $n\le100001$, the possible factors satisfy

$$
1\le a\le46,\qquad 1\le b\le17,\qquad 1\le c\le10.
$$

These are the exact integer roots of $100001$ of orders three, four, and five. The script checks these finite ranges, squarefreeness, coprimality, and the product bound. It rejects duplicate representations.

As an independent cross-check, the script also trial-factors **every integer from 1 through 100001**, retaining precisely those whose prime exponents are all at least three. It requires the resulting set to equal the representation-generated set. Neither calculation reads the Lean source or the Lean certificate generator.

The reproducible results are:

| Quantity | Value |
|---|---:|
| Positive 3-full integers in $[1,100001]$ | 129 |
| Consecutive pairs with first member in $[1,100000]$ | 0 |
| Minimum gap between successive 3-full integers in the interval | 3 |
| Only pair attaining that minimum gap | $(125,128)$ |
| Final five 3-full integers in the interval | 87808, 91125, 93312, 97336, 100000 |

The count and gap statistics are outputs of this independent numerical audit. The exported Lean nonexistence theorem does not depend on the count being 129.

## 3. The Lean proof uses prime obstructions

For each candidate first member $n$, it suffices to exhibit a prime $p$ such that either

$$
p\mid n\ \text{and}\ p^3\nmid n,
\quad\text{or}\quad
p\mid n+1\ \text{and}\ p^3\nmid n+1.
$$

The predicate `CubeFull.BadPrime n p` records exactly this obstruction. The checker first tries $2,3,5,7$. These primes settle **95,483** of the 100,000 candidates. The remaining **4,517** candidates consume explicit prime witnesses from the generated certificate. Each witness is itself checked for primality and for the required divisibility and nondivisibility.

`CubeFull.check_sound` is an induction proof that every successfully checked interval has a valid obstruction at each member. The range is divided into 25 blocks: 24 blocks of length 4096 and one final block of length 1696. The block certificates use `decide +kernel`.

The principal declarations are:

| Declaration | Meaning |
|---|---|
| `CubeFull.isCubeFull_iff_primeFactors` | Bridges the standalone predicate to the upstream prime-factor definition. |
| `CubeFull.check_sound` | Proves that an accepted interval certificate supplies a genuine obstruction for every integer in the interval. |
| `CubeFull.bounded_badPrime` | Supplies an obstruction for every $1\le n\le100000$. |
| `CubeFull.no_consecutive` | Rules out both $n$ and $n+1$ being 3-full in that range. |
| `CubeFull.refutesBoundedExistence` | Negates the complete bounded existential statement. |

The certificate-generation program is outside the trusted proof base. Lean verifies the generated data through the proved checker; the independent Python audit provides a separate reproducibility check. Compilation and axiom-audit results are reported by the repository's Cube-full audit workflow.

## 4. Reproduce the audit

Run the independent check from the repository root with a standard Python 3 installation:

```sh
python3 scripts/check_cube_full.py
```

The command emits JSON and exits unsuccessfully if the two enumerations disagree, if a consecutive pair appears, or if the stated count and minimum-gap checks fail. To include all 129 integers and their unique triples:

```sh
python3 scripts/check_cube_full.py --details
```

With the repository's pinned Lean and Mathlib dependencies installed, compile the formal proof and run its axiom audit:

```sh
python3 scripts/generate_cube_full_certificate.py
lake exe cache get
mkdir -p .lake/build/lib/lean/Additional
lake env lean -o .lake/build/lib/lean/Additional/CubeFull.olean Additional/CubeFull.lean
lake env lean CheckCubeFull.lean | tee cube-full-axioms.log
python3 scripts/check_cube_full_axioms.py cube-full-axioms.log
```

See [the Cube-full audit workflow](../.github/workflows/cube-full.yml) for the complete automated procedure, including certificate regeneration.

## 5. Scope and upstream submission status

The unbounded question recorded as `Erdos366.erdos_366.variants.weaker` asks whether **any** positive consecutive 3-full pair exists, with no upper bound. This audit leaves that question unresolved; it establishes that any such pair would have to begin above $100000$. See [the original Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/366.lean).

The inspected reduction also defines `H2`, requiring a pair beginning above $100000$. Its `main` theorem proves the conditional implication `H1 → H2 →` the unbounded statement by using `H1`; the second hypothesis is unused. This implication remains logically valid even though `H1` is false. Acceptance of a reduction verifies its implication, and does not establish that its proposed hypotheses are true or independently solvable. Our result identifies an impossible positive-proof leaf in that reduction.

As inspected on **2026-11-27**, the upstream [step-submission linter at snapshot 37c14b8](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/37c14b8ac3fd1f4f30d041fdb05c4b084078ab25/tools/lint.py) requires a reduction-step proof to contain `theorem OMA.solution : <the exact step> := ...`. Its `OMA.disproof` route applies to catalogue problems, not reduction steps. Therefore this bounded refutation cannot be submitted as an ordinary positive solution of `H1` under that inspected interface. This repository publishes it as an additional audit; it does not claim an upstream accepted step solution or a resolution of Erdős Problem 366.

Prepared for **sunnyspot114514** with assistance from **ChatGPT**. The original problem, the upstream `Nat.Full` definition, and the reduction are credited through the source links above.
