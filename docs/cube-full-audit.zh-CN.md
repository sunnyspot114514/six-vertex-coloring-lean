# 连续 3-full 整数的有界审计

[English](cube-full-audit.md)

**结论：** 对每个满足 $1\le n\le100000$ 的整数 $n$，$n$ 与 $n+1$ 至少有一个不是 3-full 数。这反驳了所核查上游归约中的有限步骤 `Erdos366.erdos_366.variants.weaker.R1.H1`。不设上界的存在性问题仍不在本结果的解决范围内；这里不作数学首创声明。

Lean 文件为 [Additional/CubeFull.lean](../Additional/CubeFull.lean)，独立数值复核程序为 [scripts/check_cube_full.py](../scripts/check_cube_full.py)。下文分别说明 Lean 证明的命题与 Python 计算提供的附加统计。

## 1. 精确审计目标

上游归约定义了如下命题：

```lean
def H1 : Prop :=
  ∃ n : ℕ, 0 < n ∧ n ≤ 100000 ∧ Nat.Full 3 n ∧ Nat.Full 3 (n + 1)
```

上界约束的是连续整数对的**第一个数**，因此检查范围需要包括 $100001$。来源为 [Erdos366 归约，快照 37c14b8](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/37c14b8ac3fd1f4f30d041fdb05c4b084078ab25/reductions/Erdos366.erdos_366.variants.weaker.R1.lean)。

Formal Conjectures 中的定义是：

```lean
def Nat.Full (k : ℕ) (n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ k ∣ n
```

对正整数而言，3-full 的意思是：每个出现的素因子，其指数都至少为 3。$1$ 没有素因子，因此满足该条件。这个定义也把 $0$ 视为 full，但审计目标明确要求 $n>0$。参见 [`Nat.Full` 定义，快照 9097e2f](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjecturesForMathlib/Data/Nat/Full.lean)。

独立 Lean 文件使用等价的谓词：

```lean
def IsCubeFull (n : Nat) : Prop :=
  ∀ p : Nat, p.Prime → p ∣ n → p ^ 3 ∣ n
```

`CubeFull.isCubeFull_iff_primeFactors` 证明它与上游 `Nat.Full 3` 所用的素因子定义等价，等价性也涵盖 $n=0$。因此，`CubeFull.refutesBoundedExistence` 的数学内容正是 $\neg H1$。

## 2. 完备的有限枚举

每个正 3-full 整数都能唯一写成

$$
n=a^3b^4c^5,
\qquad a,b,c\ge1,
$$

其中 $b,c$ 都无平方因子，且 $\gcd(b,c)=1$。$a$ 可以与 $b$ 或 $c$ 具有公共素因子。

证明只需逐个考察素因子指数 $e\ge3$。若 $e\equiv0\pmod3$，把整个指数放入 $a^3$；若 $e\equiv1\pmod3$，则 $e\ge4$，把一份该素因子放入 $b$，余下的指数 $e-4$ 放入 $a^3$；若 $e\equiv2\pmod3$，则 $e\ge5$，把一份放入 $c$，余下的指数 $e-5$ 放入 $a^3$。这给出所需表示。反过来，这种乘积中的素指数形如 $3u+4v+5w$，其中 $v,w\in\{0,1\}$ 且 $vw=0$，所以每个正指数都至少为 3。指数模 3 的余数唯一确定 $v,w$，随后也唯一确定 $u$。

若 $n\le100001$，则必有

$$
1\le a\le46,\qquad 1\le b\le17,\qquad 1\le c\le10.
$$

这些界是 $100001$ 的三次、四次、五次整数根。程序枚举这三个有限范围，检查无平方因子条件、互素条件与乘积上界，并检查表示没有重复。

程序还独立地对 **1 到 100001 的每个整数**进行试除分解，保留素因子指数全部至少为 3 的整数，并要求所得集合与表示法生成的集合完全一致。两种计算均不读取 Lean 源码或 Lean 证书生成程序。

复核结果如下：

| 项目 | 结果 |
|---|---:|
| $[1,100001]$ 内正 3-full 整数数量 | 129 |
| 首项位于 $[1,100000]$ 的连续 3-full 整数对 | 0 |
| 区间内排序后相邻 3-full 数的最小间隔 | 3 |
| 唯一达到该最小间隔的数对 | $(125,128)$ |
| 区间内最后五个 3-full 数 | 87808、91125、93312、97336、100000 |

数量与最小间隔属于独立数值复核的结果。Lean 导出的不存在性定理不依赖“数量为 129”这一统计。

## 3. Lean 证明采用素因子障碍证书

对每个待检查的首项 $n$，只需找到一个素数 $p$，使以下两种情况之一成立：

$$
p\mid n\ \text{且}\ p^3\nmid n,
\quad\text{或}\quad
p\mid n+1\ \text{且}\ p^3\nmid n+1.
$$

`CubeFull.BadPrime n p` 精确表达这个条件。检查器先尝试 $2,3,5,7$，这四个素数即可排除 100000 个候选中的 **95483** 个。余下 **4517** 个候选使用生成证书中提供的显式素数。检查器会逐一验证素性、整除关系与立方不整除关系。

`CubeFull.check_sound` 用归纳法证明：每个通过检查的区间，其每个整数都有上述障碍。整个范围分为 25 块：前 24 块各含 4096 个整数，最后一块含 1696 个整数。每块证书均使用 `decide +kernel` 验证。

主要声明如下：

| 声明 | 含义 |
|---|---|
| `CubeFull.isCubeFull_iff_primeFactors` | 将独立定义桥接到上游的素因子定义。 |
| `CubeFull.check_sound` | 证明通过区间检查意味着其中每个整数都有真实的素因子障碍。 |
| `CubeFull.bounded_badPrime` | 为每个 $1\le n\le100000$ 提供障碍。 |
| `CubeFull.no_consecutive` | 排除该范围内 $n,n+1$ 同为 3-full。 |
| `CubeFull.refutesBoundedExistence` | 否定完整的有界存在命题。 |

证书生成程序不属于可信证明基础。Lean 通过已证明正确的检查器验证生成的数据；独立 Python 程序提供另一条可复现的数值核验路径。编译与公理审计结果由仓库的 Cube-full audit 工作流报告。

## 4. 复现方法

安装标准 Python 3 后，在仓库根目录运行：

```sh
python3 scripts/check_cube_full.py
```

程序输出 JSON。如果两种枚举不一致、出现连续整数对，或数量及最小间隔检查失败，程序会以错误退出。若要输出全部 129 个整数及其唯一表示三元组，运行：

```sh
python3 scripts/check_cube_full.py --details
```

安装仓库锁定版本的 Lean 和 Mathlib 依赖后，可编译正式证明并执行公理审计：

```sh
python3 scripts/generate_cube_full_certificate.py
lake exe cache get
mkdir -p .lake/build/lib/lean/Additional
lake env lean -o .lake/build/lib/lean/Additional/CubeFull.olean Additional/CubeFull.lean
lake env lean CheckCubeFull.lean | tee cube-full-axioms.log
python3 scripts/check_cube_full_axioms.py cube-full-axioms.log
```

包括证书重新生成在内的完整自动流程见 [Cube-full audit 工作流](../.github/workflows/cube-full.yml)。

## 5. 结果范围与上游提交限制

上游 `Erdos366.erdos_366.variants.weaker` 问的是：是否存在**任意**一对正的连续 3-full 整数，不设上界。此次审计没有解决该问题，只证明若存在这样的整数对，其首项必大于 $100000$。参见 [Formal Conjectures 的原命题](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/366.lean)。

所核查归约还定义了 `H2`，要求首项大于 $100000$ 的整数对存在。它的 `main` 定理证明条件蕴含 `H1 → H2 →` 不设上界的存在命题，证明实际使用 `H1`，没有使用第二个假设。即使 `H1` 为假，这条蕴含仍然在逻辑上成立。归约被接受，说明它的蕴含关系通过了检查，并不保证提出的每个假设都为真或都可以独立完成。本结果指出了该归约中一个无法给出正向证明的步骤。

按 **2026-11-27** 核查的[上游步骤提交检查器，快照 37c14b8](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/37c14b8ac3fd1f4f30d041fdb05c4b084078ab25/tools/lint.py)，归约步骤文件必须包含 `theorem OMA.solution : <该步骤的精确命题> := ...`。`OMA.disproof` 入口适用于目录中的原始问题，没有为归约步骤提供对应入口。因此，这份有界反证无法通过所核查接口作为 `H1` 的普通正向解答提交。本仓库将其发布为附加审计，不将其标为上游已接受的步骤解答，也不声称解决了 Erdős 第 366 题。

为 **sunnyspot114514** 整理，由 **ChatGPT** 协助完成。原问题、上游 `Nat.Full` 定义与归约的来源均已在上文链接中注明。
