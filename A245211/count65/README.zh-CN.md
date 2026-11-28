# A245211：排除恰有 65 个不同素因子的无平方因子情形

本目录进一步拆分已接受的 R2 归约中的 `H3`，并给出其中第一个子目标的完整 Lean 证明。**新归约与 H1 证明均已通过原版上游检查器，判定均为 `accepted`。** 验证记录见 [GitHub Actions 运行 46066283100](https://github.com/sunnyspot114514/six-vertex-coloring-lean/actions/runs/46066283100)；这表示内核检查通过，不表示新归约或证明已由上游合并。

## 精确目标与范围

沿用上游定义

$$
a(n)=\sum_{\substack{d\mid n\\d<n}}d\,\tau(d).
$$

其中 $\tau(d)$ 是 d 的正因子个数。

本次 H1 的完整目标是：

```lean
∀ n : ℕ, Squarefree n → n.primeFactors.card = 65 →
  OeisA245211.a n ≠ n
```

这里限制的是不同素因子的个数，**没有给整数 n 设置任何大小上界**。H1 覆盖所有恰有 65 个不同素因子的无平方因子整数。

新归约把原来的 `R2.H3` 分为两部分：H1 是上述恰好 65 个素因子的情形；H2 保留平方自由整数中，素因子个数至少为 67、为奇数且不是正指数素数幂的情形。原 H3 的下界是 65，排除 65 后，由奇数条件可把剩余下界提高到 67。**这个剩余 H2 仍未解决；完整 H3 和原猜想也不在本次证明的范围内。**

## 证明思路

假设存在满足 H1 条件的固定点 `a n = n`，共享的循环归约会给出长度 65 的素数循环及乘子：

$$
2p_{i+1}+1=d_i p_i,\qquad
\prod_{i=0}^{64}d_i=2^{65}+1,\qquad p_i>2^{64}.
$$

因子分解为

$$
2^{65}+1=3\cdot11\cdot131\cdot2731\cdot409891\cdot7623851.
$$

除唯一的因子 3 外，其余五个因子都模 5 余 1。将因子 3 所在位置旋转到 0，并使用已证明的中性因子删除引理，模 5 的投影列表只剩 `[(3, 0)]`；其余因子位于哪里不再影响此检查。

种子递推为 `c₀ = 0`、`cⱼ₊₁ = dⱼ cⱼ + 2ʲ`。循环闭合与 `∏dᵢ − 2⁶⁵ = 1` 给出 `p₀ = c₆₅`。模 5 投影中，`d₀ ≡ 3`，对 `j = 1, …, 64` 均有 `dⱼ ≡ 1`；又因 `c₀ = 0`，第一步得到 `c₁ = 1`。因此 `c₆₅ ≡ 2⁶⁵ − 1 ≡ 1 (mod 5)`。素数剩余类沿循环的前两次转移便是

$$
p_0\equiv1\ \longmapsto\ p_1\equiv1\ \longmapsto\ p_2\equiv0\pmod5.
$$

这与 `p₂` 是大于 5 的素数矛盾。Lean 中的闭合计算证书是 `positionTest 65 5 [(3, 0)] = false`，使用 `decide +kernel`；真实素数循环必通过该检查的结论由共享桥接定理提供。这里没有对 n 枚举，也没有把 Python 计算作为证明假设。

## 文件与提交顺序

- [新归约](reductions/OeisA245211.conjecture.R2.H3.R1.lean)：声明 H1、剩余 H2，并证明二者推出原 `R2.H3`。
- [H1 单文件证明](proofs/OeisA245211.conjecture.R2.H3.R1.H1.lean)：目标为精确的 `OMA.R_OeisA245211_conjecture_R2_H3_R1.H1`。
- [Count65Main.lean](Count65Main.lean)：65 因子情形的短证明模块。
- [assemble_count65.py](assemble_count65.py)：从五个共享模块及 `Count65Main.lean` 组装 H1 单文件。
- [独立验证工作流](../../.github/workflows/a245211-count65.yml)：使用原版上游 lint 和检查器分别验证两份提交。

上游提交应分两步：**先提交并等待新归约合并，再提交它生成的 H1 叶子证明。** 工作流为本地验证注册新归约模块，不表示该归约已经被上游接受。

## 可复现验证

使用与 H2 项目相同的固定版本：

- Formal Conjectures：`9097e2f90e66d2f6244209cb1c07f7120d17ec53`。
- Open Math Agents：`d4827fcc0af9b8327e56e1eb335394e1cf6514c6`。
- Lean：4.33.1；Mathlib：`0df444a360eaa60ab8c11dca51a86af692955474`，由该 Formal Conjectures 提交的工具链与依赖锁定。

工作流先重新运行组装器，并要求生成结果与已跟踪的 H1 单文件逐字相同。随后复制固定版本的 R2 和本目录的新归约到 Formal Conjectures 的 `OMAReductions` 库，使用 `lean-action` 只构建新的 R1 模块及其依赖，再调用**未经修改的 `tools/check.sh`**，依次检查归约与 H1。

上游每份提交的 1800 秒编译期限、精确目标检查和公理白名单审计全部保留。工作流分别输出并断言两个 verdict 为 `accepted`，最后保存两份 verdict、两份 lint 结果以及提交源码和原版检查脚本的 SHA-256。

此次通过的源提交是 `1092337264737c2b8ffc771cb1e1edea6fd28717`。北京时间 2026-11-28 04:52，归约和 H1 的完整检查均返回 `accepted`，公理依赖均为 `[propext, Classical.choice, Quot.sound]`。H1 单文件的 SHA-256 为 `ab8b319b44db4d0b8392b1a6d5c56ee509b742bebba1539c61c43db9034af761`。可查看 [验证清单](verification/verification.json)、[归约判定](verification/github-reduction-verdict.json) 和 [H1 判定](verification/github-h1-verdict.json)。

该工作流采用独立的并发组；本目录位于 `A245211/count65/`，新增文件不匹配旧 H2 工作流的 `A245211/*.lean` 触发规则。共享数学模块改动仍会触发相应验证。

## 依赖与已有工作

证明使用固定版本 R2 归约中的公开引理，并复用本仓库独立编写的循环、因子分配和模检验模块。循环论证的数学思路也见于上游 [R2.H1 的 PR #7273](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7273)。原 `R2.H2` 已由 MakisChristou 通过 [PR #9600](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9600) 解决；本目录处理的是其 `r < 65` 范围之外的 `r = 65` 子情形，不主张全猜想或该数学事实的首次发现。

新归约已于 2026-11-28 11:48:05（北京时间） 提交为[上游 PR #19267](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19267)，当前仍开放、尚未合并。H1 证明已在本仓库验证并发布，待父归约合并后再单独向上游提交。上游接受状态应以实际 PR 和合并记录为准。
