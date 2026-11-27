# 六顶点图染色引理

[![Verify](https://github.com/sunnyspot114514/six-vertex-coloring-lean/actions/workflows/verify.yml/badge.svg)](https://github.com/sunnyspot114514/six-vertex-coloring-lean/actions/workflows/verify.yml)

[English](README.md) · [完整初等证明](docs/proof.zh-CN.md) · [Lean 定理](SixVertex/Coloring.lean)

**对任意至多六个顶点的无三角形简单图，无论怎样把边染成红、蓝两色，都能给顶点染红、蓝两色，使红边不连接两个红点、蓝边不连接两个蓝点。**

这个项目提供一份简短的结构证明、一份独立编写的完整穷举程序，以及一个独立的 Lean 形式化项目。

## 新增算术结果：A245211 中恰有 65 个素因子的情形

对加权真因子和

$$
a(n)=\sum_{\substack{d\mid n\\d<n}} d\,\tau(d),
$$

其中 $\tau(d)$ 是正因子个数，本次的新定理是：

**任意恰有 65 个不同素因子的无平方因子整数，都满足 $a(n)\ne n$。整数 $n$ 的大小没有上界。**

[H1 单文件证明](A245211/count65/proofs/OeisA245211.conjecture.R2.H3.R1.H1.lean) 的精确目标为：

```lean
∀ n : ℕ, Squarefree n → n.primeFactors.card = 65 →
  OeisA245211.a n ≠ n
```

证明先把假设存在的固定点归约为大素数组成的循环，再利用因子分解

$$
2^{65}+1=3\cdot11\cdot131\cdot2731\cdot409891\cdot7623851.
$$

除 3 外，其余因子都模 5 余 1。把因子 3 的位置旋转到首位，使用已经证明的投影引理后，模 5 的投影列表只剩 `[(3, 0)]`。其起始剩余类被迫为 1，接下来的素数剩余类沿 $1\to1\to0\pmod5$ 转移，与这些素数大于 5 矛盾。这里的有限计算是数学归约后的内核证书，没有对原整数设置搜索上界。

配套的[新归约提案](A245211/count65/reductions/OeisA245211.conjecture.R2.H3.R1.lean)把现有 `R2.H3` 分成上述恰好 65 个素因子的情形，以及平方自由整数中，**素因子个数至少为 67、为奇数且不是正指数素数幂**的剩余情形。后者在本项目中仍未解决。**本结果不等于完整解决 H3，也不等于解决整个 OEIS 猜想。** 详见[证明与验证说明](A245211/count65/README.zh-CN.md)。

### A245211 的验证与发布状态

两项独立的 GitHub CI 均已成功：

| 结果 | 成功的 CI 运行 | 对应源码提交 |
|---|---|---|
| 新的 65 因子情形及其 H3 归约提案 | [46066283100](https://github.com/sunnyspot114514/six-vertex-coloring-lean/actions/runs/46066283100) | [`109233726473`](https://github.com/sunnyspot114514/six-vertex-coloring-lean/commit/1092337264737c2b8ffc771cb1e1edea6fd28717) |
| 对既有 R2.H2 结果的独立实现 | [46064959548](https://github.com/sunnyspot114514/six-vertex-coloring-lean/actions/runs/46064959548) | [`b8dd8c8e5f72`](https://github.com/sunnyspot114514/six-vertex-coloring-lean/commit/b8dd8c8e5f726ab70812fadb20c39289b2e79444) |

原版上游检查器对 **H2、新归约、H1 三份提交均返回 `accepted`**；三份公理报告均仅包含 `propext`、`Classical.choice`、`Quot.sound`。

[count65 工作流](.github/workflows/a245211-count65.yml)使用未经修改的上游检查器，分别检查归约与 H1，保留每份提交的时间限制和公理审计，并保存 verdict 与源码哈希。[H2 工作流](.github/workflows/a245211.yml)独立运行。

**新归约与 65 因子证明目前仅发布在本仓库；这两份文件尚未向上游提交 PR，也没有上游合并记录。** 向上游提交时，应先等待新归约被接受，再提交它产生的 H1 叶子证明。

### 已有 H2 结果：独立实现与优先权说明

[H2 实现](A245211/submission/OeisA245211.conjecture.R2.H2.lean)覆盖不同素因子个数为
`15、21、33、35、39、45、51、55、57、63` 的无平方因子整数，同样不限制整数本身的大小。这正是 3 至 64 之间不是正指数素数幂的奇数个数情形。

**MakisChristou 的[上游 PR #9600](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9600)在本实现完成验证前，已经解决 H2 并被合并。** 本仓库保留的是独立、可复现的实现，不声称首次解决，也不向上游重复提交 H2。其[中文说明](A245211/README.zh-CN.md)记录了循环归约、模运算证书及结果范围。

## 新增有限审计：相邻三次满数

[![Cube-full audit](https://github.com/sunnyspot114514/six-vertex-coloring-lean/actions/workflows/cube-full.yml/badge.svg)](https://github.com/sunnyspot114514/six-vertex-coloring-lean/actions/workflows/cube-full.yml)

[新增审计](docs/cube-full-audit.zh-CN.md)证明：不存在 `1 ≤ n ≤ 100000`，使 `n` 和 `n + 1` 同时为三次满数。它否定了上游拆分提出的有限假设 `Erdos366.erdos_366.variants.weaker.R1.H1`，附有 [Lean 证书](Additional/CubeFull.lean)和独立算术检查程序。结果的范围是这个有限假设；Erdős #366 的无界问题不在其中。

## 证明的关键

这样的图最多删掉一条边就能成为二分图。如果它原本不是二分图，必然包含一个没有弦的五边形；圈外至多一个顶点，无三角形条件又限制了它的连边方式，因此可以直接分析全部结构。

给删边后的图按二分部正常染色。如果补回的那条边违反要求，就把所有顶点的红蓝颜色整体互换。那条边得到修复，其他边仍然连接异色顶点。详见[完整证明](docs/proof.zh-CN.md)。

## 验证结果与复现

独立 Python 程序枚举全部六顶点标号简单图：

| 类别 | 数量 |
|---|---:|
| 全部图 | 32,768 |
| 无三角形图 | 5,789 |
| 已经是二分图 | 5,177 |
| 恰需删一条边成为二分图 | 612 |
| 已核验的“图／边染色”组合 | 294,987 |
| 反例 | 0 |

Lean 使用内核归约验证有限图性质，再严格连接到 `SimpleGraph` 上的命题，并覆盖全部 `k ≤ 6` 的情况。Python 检查结果不作为 Lean 定理的公理或受信任输入。

GitHub Actions 会编译项目、用 `leanchecker` 回放项目模块，并检查最终定理的公理依赖，只允许 `propext`、`Classical.choice`、`Quot.sound`。上方徽章显示本仓库当前的实际验证状态。

安装 [elan](https://github.com/leanprover/elan) 后运行：

```bash
python3 scripts/check_exhaustive.py
lake update
lake exe cache get
lake build
lake env leanchecker SixVertex
lake env lean Check.lean
```

版本固定为 Lean **4.33.1** 和 Mathlib 提交 **0df444a360eaa60ab8c11dca51a86af692955474**。

## 来源与署名

命题对应 Left to Solve 中 Erdős #151 某个变体的 **R1.H2 子步骤**，拆分由 **dk8827** 提出，见 [PR #4050](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4050)。

准备发布时，我们核实 **Salofe 的 [PR #5331](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5331)** 已于 **2026 年 11 月 27 日北京时间 19:22:31** 被接受并合并。此前网页的“开放”状态存在滞后。该形式化同样使用有限图检查与整体换色；已有形式化的优先权属于该贡献者，本仓库不声称首次解决。

本项目为 **sunnyspot114514** 准备，由 **ChatGPT** 协助完成。

## 范围

这是一条明确、有限的图论引理及其可复现证明。**它不等于解决 Erdős #151，也不等于解决其 `cliqueFree_four` 变体或该拆分的其他假设。** 人类可读证明使用五边形结构；Lean 实现通过计算验证对应的有限图性质。

